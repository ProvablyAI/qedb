//! The queries of the paper on a `Transaction(tx_id, account_id, trade_date, price,
//! expected_price)` table, composed from the primitives:
//!
//! - `QTot`: `SELECT SUM(price) FROM Transaction WHERE account_id = 5938 AND trade_date =
//!   '2025-01-01'`;
//! - `QCntTx`: `SELECT COUNT(*) FROM Transaction WHERE trade_date BETWEEN '2025-01-01' AND
//!   '2025-03-31'`;
//! - `QMatch`: `SELECT tx_id, price, expected_price, price = expected_price FROM Transaction WHERE
//!   trade_date = '2025-04-05'`.
//!
//! Equality filters use an inverted index (App. E.1): for each value of a column, the handle of
//! the set of rows holding it, computed at preprocessing. Dates are integers `yyyymmdd`.
//!
//! Run with `cargo bench`; `QEDB_LOG_ROWS=10,12,14` sets the table sizes (`2^k` rows).

use ark_bls12_381::Fr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{Rng, SeedableRng, rngs::StdRng};
use qedb::Error;
use qedb::basic::complement::ComplementProof;
use qedb::basic::intersection::IntersectionProof;
use qedb::basic::read::ReadProof;
use qedb::derived::sign_check::SignCheckProof;
use qedb::derived::sum_check::SumCheckProof;
use qedb::handle::{
    CommittedSet, CommittedSlice, Set, SetHandle, Slice, SliceHandle, Universe, UniverseHandle,
};
use qedb::setup::{Srs, VerifierKey};
use qedb::transcript::Transcript;
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// Bits of the range checks of the range query: date differences are far below `2^32`.
const ELL: usize = 32;

const ACCOUNT: u64 = 5938;
const TOT_DATE: u64 = 20250101;
const QUARTER: (u64, u64) = (20250101, 20250331);
const MATCH_DATE: u64 = 20250405;

// ---------------------------------------------------------------------------------------------
// The table and its preprocessing.
// ---------------------------------------------------------------------------------------------

struct Table {
    tx_id: Vec<u64>,
    account_id: Vec<u64>,
    trade_date: Vec<u64>,
    price: Vec<u64>,
    expected_price: Vec<u64>,
}

impl Table {
    fn generate(n: usize, rng: &mut StdRng) -> Self {
        let mut table = Self {
            tx_id: (1..=n as u64).collect(),
            account_id: (0..n).map(|_| rng.gen_range(5000..6000)).collect(),
            trade_date: (0..n).map(|_| date(rng.gen_range(0..365))).collect(),
            price: (0..n).map(|_| rng.gen_range(1..100_000)).collect(),
            expected_price: vec![],
        };
        table.expected_price = table
            .price
            .iter()
            .map(|&p| {
                if rng.gen_bool(0.8) {
                    p
                } else {
                    p + rng.gen_range(1..100)
                }
            })
            .collect();
        // A few transactions of the account on the date of QTot.
        for j in (0..n).step_by(n / 4).take(4) {
            table.account_id[j] = ACCOUNT;
            table.trade_date[j] = TOT_DATE;
        }
        table
    }
}

/// The date `yyyymmdd` of the `day`-th day of 2025, from 0.
const fn date(day: u64) -> u64 {
    const DAYS: [u64; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    let (mut month, mut day) = (0, day);
    while day >= DAYS[month] {
        day -= DAYS[month];
        month += 1;
    }
    20250000 + (month as u64 + 1) * 100 + day + 1
}

/// An inverted index: for each value of a column, the set of rows holding it. A value not in the
/// column has the empty set.
struct Index {
    sets: HashMap<u64, CommittedSet>,
    empty: CommittedSet,
}

impl Index {
    fn build(srs: &Srs, column: &[u64]) -> Self {
        let mut rows: HashMap<u64, Vec<usize>> = HashMap::new();
        for (row, &value) in column.iter().enumerate() {
            rows.entry(value).or_default().push(row);
        }
        let sets = rows
            .into_iter()
            .map(|(value, rows)| (value, Set::new(rows).commit(srs).unwrap()))
            .collect();
        let empty = Set::new([]).commit(srs).unwrap();
        Self { sets, empty }
    }

    fn get(&self, value: u64) -> &CommittedSet {
        self.sets.get(&value).unwrap_or(&self.empty)
    }

    fn handles(&self) -> IndexHandles {
        IndexHandles {
            sets: self
                .sets
                .iter()
                .map(|(&value, set)| (value, set.handle()))
                .collect(),
            empty: self.empty.handle(),
        }
    }
}

/// The handles of an [`Index`].
struct IndexHandles {
    sets: HashMap<u64, SetHandle>,
    empty: SetHandle,
}

impl IndexHandles {
    fn get(&self, value: u64) -> SetHandle {
        self.sets.get(&value).copied().unwrap_or(self.empty)
    }
}

/// The prover's view: the table, committed.
struct Database {
    universe: Universe,
    tx_id: CommittedSlice,
    trade_date: CommittedSlice,
    price: CommittedSlice,
    expected_price: CommittedSlice,
    accounts: Index,
    dates: Index,
}

impl Database {
    fn preprocess(srs: &Srs, table: &Table) -> Self {
        let column = |values: &[u64]| {
            Slice::new(values.iter().map(|&x| Fr::from(x)).collect())
                .commit(srs)
                .unwrap()
        };
        Self {
            universe: Universe::new(srs, table.tx_id.len()).unwrap(),
            tx_id: column(&table.tx_id),
            trade_date: column(&table.trade_date),
            price: column(&table.price),
            expected_price: column(&table.expected_price),
            accounts: Index::build(srs, &table.account_id),
            dates: Index::build(srs, &table.trade_date),
        }
    }

    /// The verifier's view: the handles only.
    fn digest(&self) -> Digest {
        Digest {
            universe: self.universe.handle(),
            tx_id: self.tx_id.handle(),
            trade_date: self.trade_date.handle(),
            price: self.price.handle(),
            expected_price: self.expected_price.handle(),
            accounts: self.accounts.handles(),
            dates: self.dates.handles(),
        }
    }
}

struct Digest {
    universe: UniverseHandle,
    tx_id: SliceHandle,
    trade_date: SliceHandle,
    price: SliceHandle,
    expected_price: SliceHandle,
    accounts: IndexHandles,
    dates: IndexHandles,
}

fn intersect(a: &CommittedSet, b: &CommittedSet) -> Set {
    a.set().difference(&a.set().difference(b.set()))
}

fn rows_of(values: &[u64], keep: impl Fn(u64) -> bool) -> Set {
    Set::new((0..values.len()).filter(|&j| keep(values[j])))
}

// ---------------------------------------------------------------------------------------------
// QTot: the intersection of two index sets, and a sum check of price on it.
// ---------------------------------------------------------------------------------------------

#[derive(CanonicalSerialize, CanonicalDeserialize)]
struct TotProof {
    selection: SetHandle,
    intersection: IntersectionProof,
    sum: SumCheckProof,
}

fn tot_transcript() -> Transcript {
    let mut transcript = Transcript::new("qedb: QTot");
    transcript.append("account_id", &ACCOUNT);
    transcript.append("trade_date", &TOT_DATE);
    transcript
}

fn prove_tot(srs: &Srs, db: &Database, table: &Table) -> (u64, TotProof) {
    let transcript = &mut tot_transcript();
    let (account, day) = (db.accounts.get(ACCOUNT), db.dates.get(TOT_DATE));
    let selection = intersect(account, day).commit(srs).unwrap();
    let sum = selection.set().rows().iter().map(|&j| table.price[j]).sum();

    let intersection =
        IntersectionProof::prove(srs, &[account, day], &selection, transcript).unwrap();
    let sum_proof = SumCheckProof::prove(
        srs,
        &db.universe,
        &db.price,
        &selection,
        Fr::from(sum),
        transcript,
    )
    .unwrap();
    let proof = TotProof {
        selection: selection.handle(),
        intersection,
        sum: sum_proof,
    };
    (sum, proof)
}

fn verify_tot(vk: &VerifierKey, digest: &Digest, sum: u64, proof: &TotProof) -> Result<(), Error> {
    let transcript = &mut tot_transcript();
    let sets = [digest.accounts.get(ACCOUNT), digest.dates.get(TOT_DATE)];
    proof
        .intersection
        .verify(&sets, proof.selection, transcript)?;
    proof.sum.verify(
        vk,
        digest.universe,
        digest.price,
        proof.selection,
        Fr::from(sum),
        transcript,
    )
}

// ---------------------------------------------------------------------------------------------
// QCntTx: the range query of App. E.2, and a sum check of the all-ones slice.
//
// The prover sends X_in = {α ≤ v ≤ β}, X_< = {v < α}, X_> = {v > β} and C = X_< ∪ X_>, and the
// verifier checks:
// - the partition: C = ∗ ∖ X_in and X_> = C ∖ X_<;
// - one sign check of v − α on X_in, (α − 1) − v on X_<, v − (β + 1) on X_>;
// - one sign check of β − v on X_in.
// The sign checks are within the subsets (as Table 2's), not over all rows.
// ---------------------------------------------------------------------------------------------

#[derive(CanonicalSerialize, CanonicalDeserialize)]
struct CntProof {
    selection: SetHandle,
    below: SetHandle,
    above: SetHandle,
    outside: SetHandle,
    complement: ComplementProof,
    split: ComplementProof,
    lower: SignCheckProof,
    upper: SignCheckProof,
    count: SumCheckProof,
}

fn cnt_transcript() -> Transcript {
    let mut transcript = Transcript::new("qedb: QCntTx");
    transcript.append("from", &QUARTER.0);
    transcript.append("to", &QUARTER.1);
    transcript
}

fn prove_cnt(srs: &Srs, db: &Database, table: &Table) -> (u64, CntProof) {
    let transcript = &mut cnt_transcript();
    let (u, ones, v) = (&db.universe, db.universe.ones(), &db.trade_date);
    let (alpha, beta) = QUARTER;
    let constant = |c: u64| ones * Fr::from(c);
    let selection = rows_of(&table.trade_date, |d| (alpha..=beta).contains(&d))
        .commit(srs)
        .unwrap();
    let below = rows_of(&table.trade_date, |d| d < alpha)
        .commit(srs)
        .unwrap();
    let above = rows_of(&table.trade_date, |d| d > beta)
        .commit(srs)
        .unwrap();
    let outside = u
        .rows()
        .set()
        .difference(selection.set())
        .commit(srs)
        .unwrap();
    let count = selection.set().rows().len() as u64;

    let complement =
        ComplementProof::prove(srs, u.rows(), &selection, &outside, transcript).unwrap();
    let split = ComplementProof::prove(srs, &outside, &below, &above, transcript).unwrap();
    let lower = SignCheckProof::prove(
        srs,
        &[
            (&(v - &constant(alpha)), &selection),
            (&(&constant(alpha - 1) - v), &below),
            (&(v - &constant(beta + 1)), &above),
        ],
        ELL,
        transcript,
    )
    .unwrap();
    let upper = SignCheckProof::prove(
        srs,
        &[(&(&constant(beta) - v), &selection)],
        ELL,
        transcript,
    )
    .unwrap();
    let count_proof =
        SumCheckProof::prove(srs, u, ones, &selection, Fr::from(count), transcript).unwrap();
    let proof = CntProof {
        selection: selection.handle(),
        below: below.handle(),
        above: above.handle(),
        outside: outside.handle(),
        complement,
        split,
        lower,
        upper,
        count: count_proof,
    };
    (count, proof)
}

fn verify_cnt(
    vk: &VerifierKey,
    digest: &Digest,
    count: u64,
    proof: &CntProof,
) -> Result<(), Error> {
    let transcript = &mut cnt_transcript();
    let (u, ones, v) = (digest.universe, digest.universe.ones, digest.trade_date);
    let (alpha, beta) = QUARTER;
    let constant = |c: u64| ones * Fr::from(c);

    proof
        .complement
        .verify(u.rows, proof.selection, proof.outside, transcript)?;
    proof
        .split
        .verify(proof.outside, proof.below, proof.above, transcript)?;
    let lower = [
        (v - constant(alpha), proof.selection),
        (constant(alpha - 1) - v, proof.below),
        (v - constant(beta + 1), proof.above),
    ];
    proof.lower.verify(vk, &lower, ELL, transcript)?;
    let upper = [(constant(beta) - v, proof.selection)];
    proof.upper.verify(vk, &upper, ELL, transcript)?;
    proof
        .count
        .verify(vk, u, ones, proof.selection, Fr::from(count), transcript)
}

// ---------------------------------------------------------------------------------------------
// QMatch: three reads on an index set; the verifier computes price = expected_price itself.
// ---------------------------------------------------------------------------------------------

#[derive(PartialEq, Eq, Debug)]
struct MatchAnswer {
    rows: Vec<usize>,
    tx_id: Vec<Fr>,
    price: Vec<Fr>,
    expected_price: Vec<Fr>,
    matches: Vec<bool>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
struct MatchProof {
    reads: [ReadProof; 3],
}

fn match_transcript() -> Transcript {
    let mut transcript = Transcript::new("qedb: QMatch");
    transcript.append("trade_date", &MATCH_DATE);
    transcript
}

fn prove_match(srs: &Srs, db: &Database) -> (MatchAnswer, MatchProof) {
    let transcript = &mut match_transcript();
    let day = db.dates.get(MATCH_DATE);
    let mut read = |column| ReadProof::prove(srs, column, day, transcript).unwrap();
    let (tx_id, tx_id_proof) = read(&db.tx_id);
    let (price, price_proof) = read(&db.price);
    let (expected_price, expected_proof) = read(&db.expected_price);
    let matches = price
        .iter()
        .zip(&expected_price)
        .map(|(a, b)| a == b)
        .collect();
    let answer = MatchAnswer {
        rows: day.set().rows().to_vec(),
        tx_id,
        price,
        expected_price,
        matches,
    };
    let proof = MatchProof {
        reads: [tx_id_proof, price_proof, expected_proof],
    };
    (answer, proof)
}

fn verify_match(
    vk: &VerifierKey,
    digest: &Digest,
    answer: &MatchAnswer,
    proof: &MatchProof,
) -> Result<(), Error> {
    let transcript = &mut match_transcript();
    let day = digest.dates.get(MATCH_DATE);
    let columns = [
        (digest.tx_id, &answer.tx_id),
        (digest.price, &answer.price),
        (digest.expected_price, &answer.expected_price),
    ];
    for ((column, values), read) in columns.into_iter().zip(&proof.reads) {
        read.verify(vk, column, day, &answer.rows, values, transcript)?;
    }
    // The computed column, from the verified values.
    let matches: Vec<bool> = answer
        .price
        .iter()
        .zip(&answer.expected_price)
        .map(|(a, b)| a == b)
        .collect();
    if matches != answer.matches {
        return Err(Error::Rejected("QMatch"));
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Timing.
// ---------------------------------------------------------------------------------------------

fn time<T>(f: impl FnOnce() -> T) -> (T, Duration) {
    let start = Instant::now();
    let out = f();
    (out, start.elapsed())
}

/// The fastest of five runs.
fn best(mut f: impl FnMut()) -> Duration {
    (0..5).map(|_| time(&mut f).1).min().unwrap_or_default()
}

fn row(
    query: &str,
    answer: impl std::fmt::Display,
    prove: Duration,
    verify: Duration,
    size: usize,
) {
    println!(
        "  {query:<7} {answer:>10}  prove {:>10.2?}  verify {:>9.2?}  proof {size:>7} B",
        prove, verify
    );
}

fn main() {
    let logs: Vec<u32> = std::env::var("QEDB_LOG_ROWS")
        .unwrap_or_else(|_| "10,12,14,16".into())
        .split(',')
        .map(|k| {
            k.trim()
                .parse()
                .expect("QEDB_LOG_ROWS: comma-separated integers")
        })
        .collect();

    for log in logs {
        let n = 1usize << log;
        let rng = &mut StdRng::seed_from_u64(log.into());
        let table = Table::generate(n, rng);
        let (srs, setup) = time(|| Srs::setup(n, rng).unwrap());
        let (db, preprocessing) = time(|| Database::preprocess(&srs, &table));
        let digest = db.digest();
        let vk = srs.verifier_key();
        println!(
            "2^{log} rows: setup {setup:.2?}, preprocessing {preprocessing:.2?}, verifier key {} B",
            vk.compressed_size()
        );

        // QTot
        let ((sum, proof), prove) = time(|| prove_tot(&srs, &db, &table));
        let expected: u64 = (0..n)
            .filter(|&j| table.account_id[j] == ACCOUNT && table.trade_date[j] == TOT_DATE)
            .map(|j| table.price[j])
            .sum();
        assert_eq!(sum, expected);
        assert_eq!(verify_tot(&vk, &digest, sum, &proof), Ok(()));
        assert!(verify_tot(&vk, &digest, sum + 1, &proof).is_err());
        let verify = best(|| verify_tot(&vk, &digest, sum, &proof).unwrap());
        row("QTot", sum, prove, verify, proof.compressed_size());

        // QCntTx
        let ((count, proof), prove) = time(|| prove_cnt(&srs, &db, &table));
        let in_quarter = |&d: &u64| (QUARTER.0..=QUARTER.1).contains(&d);
        assert_eq!(
            count,
            table.trade_date.iter().filter(|d| in_quarter(d)).count() as u64
        );
        assert_eq!(verify_cnt(&vk, &digest, count, &proof), Ok(()));
        assert!(verify_cnt(&vk, &digest, count + 1, &proof).is_err());
        let verify = best(|| verify_cnt(&vk, &digest, count, &proof).unwrap());
        row("QCntTx", count, prove, verify, proof.compressed_size());

        // QMatch
        let ((answer, proof), prove) = time(|| prove_match(&srs, &db));
        let rows: Vec<usize> = (0..n)
            .filter(|&j| table.trade_date[j] == MATCH_DATE)
            .collect();
        assert_eq!(answer.rows, rows);
        assert_eq!(verify_match(&vk, &digest, &answer, &proof), Ok(()));
        // A wrong match, or with no row, a row that is not selected.
        let wrong = if answer.rows.is_empty() {
            let f = |column: &[u64]| vec![Fr::from(column[0])];
            MatchAnswer {
                rows: vec![0],
                tx_id: f(&table.tx_id),
                price: f(&table.price),
                expected_price: f(&table.expected_price),
                matches: vec![table.price[0] == table.expected_price[0]],
            }
        } else {
            let mut matches = answer.matches.clone();
            matches[0] = !matches[0];
            MatchAnswer {
                matches,
                rows: answer.rows.clone(),
                tx_id: answer.tx_id.clone(),
                price: answer.price.clone(),
                expected_price: answer.expected_price.clone(),
            }
        };
        assert!(verify_match(&vk, &digest, &wrong, &proof).is_err());
        let verify = best(|| verify_match(&vk, &digest, &answer, &proof).unwrap());
        let rows = format!("{} rows", answer.rows.len());
        row("QMatch", rows, prove, verify, proof.compressed_size());
    }
}
