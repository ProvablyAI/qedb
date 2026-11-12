//! Proof that sets `D₁, …, Dₖ` have no common row, shared by the intersection and union tests.
//!
//! The prover sends `[P_{Dᵢ}(τ)]₂` and Bézout coefficients `[qᵢ(τ)]₁` with `Σ qᵢ · P_{Dᵢ} = 1`,
//! which exist if and only if `gcd(P_{D₁}, …, P_{Dₖ}) = 1`. Each test ties every `Dᵢ` to its
//! sets with an equation `e(aᵢ, [P_{Dᵢ}]₂) = e(tᵢ, [1]₂)`. The verifier checks these and
//! `Σᵢ e([qᵢ]₁, [P_{Dᵢ}]₂) = e([1]₁, [1]₂)`, batched with a challenge `ρ` as
//! `Σᵢ e(ρⁱaᵢ + [qᵢ]₁, [P_{Dᵢ}]₂) = e([1]₁ + Σᵢ ρⁱtᵢ, [1]₂)`.
//!
//! The proof must have exactly one `Dᵢ` and one `qᵢ` per equation: an extra pair `([1]₁, [1]₂)`
//! would satisfy the Bézout equation for any sets.

use super::divide_exact;
use crate::Error;
use crate::handle::Set;
use crate::setup::{Domain, Srs};
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::PrimeGroup;
use ark_ec::pairing::Pairing;
use ark_ff::{Field, Zero, batch_inversion};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CoprimeProof {
    /// `[P_{Dᵢ}(τ)]₂`.
    pub sets_g2: Vec<G2Projective>,
    /// `[qᵢ(τ)]₁` with `Σ qᵢ · P_{Dᵢ} = 1`.
    pub bezout_g1: Vec<G1Projective>,
}

impl CoprimeProof {
    /// Proves that `sets` have no common row; `test` names the calling test in errors.
    pub fn prove(srs: &Srs, sets: &[Set], test: &'static str) -> Result<Self, Error> {
        let domain = srs.domain();
        let polynomials = in_batches(sets, |set| set.characteristic(domain))?;
        let bezout = bezout_coefficients(domain, sets, &polynomials, test)?;

        Ok(Self {
            sets_g2: in_batches(&polynomials, |p| srs.commit_g2(p))?,
            bezout_g1: in_batches(&bezout, |q| srs.commit_g1(q))?,
        })
    }

    /// Checks `e(aᵢ, [P_{Dᵢ}]₂) = e(tᵢ, [1]₂)` for the pairs `(aᵢ, tᵢ)`, and the Bézout equation.
    pub fn verify(&self, pairs: &[(G1Projective, G1Projective)], rho: Fr) -> bool {
        let k = pairs.len();
        if k == 0 || self.sets_g2.len() != k || self.bezout_g1.len() != k {
            return false;
        }

        let mut g1 = Vec::with_capacity(k + 1);
        let mut g2 = Vec::with_capacity(k + 1);
        let mut rho_i = Fr::ONE;
        let mut rhs = G1Projective::generator();
        for (((a, t), set), q) in pairs.iter().zip(&self.sets_g2).zip(&self.bezout_g1) {
            rho_i *= rho;
            g1.push(*a * rho_i + q);
            g2.push(*set);
            rhs += *t * rho_i;
        }
        g1.push(-rhs);
        g2.push(G2Projective::generator());

        Bls12_381::multi_pairing(g1, g2).is_zero()
    }
}

/// Bézout coefficients `qᵢ` with `Σ qᵢ · P_{Dᵢ} = 1`, for sets `Dᵢ` with no common row.
///
/// Every row of `V = ∪ Dᵢ` is assigned to one set that misses it, and `Gᵢ` is the polynomial of
/// degree `< |V|` equal to `1` on the rows `Aᵢ` assigned to `i` and to `0` on the other rows of
/// `V`: `Σ Gᵢ = 1`, as both sides have degree `< |V|` and agree on `V`. `Gᵢ` vanishes on `Dᵢ`, so
/// `qᵢ = Gᵢ / P_{Dᵢ}` is a polynomial. It is computed on the rows of `Tᵢ = V ∖ Dᵢ` when every `Tᵢ`
/// is small ([`on_rows`]), and otherwise with FFTs on the whole domain ([`on_domain`]), which are
/// faster then: both give the same `qᵢ`.
fn bezout_coefficients(
    domain: &Domain,
    sets: &[Set],
    polynomials: &[DensePolynomial<Fr>],
    test: &'static str,
) -> Result<Vec<DensePolynomial<Fr>>, Error> {
    // An empty Dᵢ has P_{Dᵢ} = 1: qᵢ = 1, and 0 for the other sets.
    if let Some(empty) = sets.iter().position(|set| set.rows().is_empty()) {
        return Ok((0..sets.len())
            .map(|i| {
                let q = if i == empty { vec![Fr::ONE] } else { vec![] };
                DensePolynomial::from_coefficients_vec(q)
            })
            .collect());
    }

    let (union, assigned) = assign(domain, sets, test)?;
    let small = |set: &Set| (union.rows().len() - set.rows().len()) * SMALL <= domain.size();
    if sets.iter().all(small) {
        on_rows(domain, &union, &assigned, sets)
    } else {
        on_domain(domain, &union, &assigned, polynomials)
    }
}

/// `V = ∪ Dᵢ`, and the rows `Aᵢ` assigned to each set: every row of `V` to the first set that
/// misses it.
fn assign(domain: &Domain, sets: &[Set], test: &'static str) -> Result<(Set, Vec<Set>), Error> {
    let mut assigned = vec![Vec::new(); sets.len()];
    let mut in_union = vec![false; domain.size()];
    for &row in sets.iter().flat_map(Set::rows) {
        if !in_union[row] {
            in_union[row] = true;
            let i = sets
                .iter()
                .position(|set| set.rows().binary_search(&row).is_err())
                .ok_or(Error::InvalidWitness(test))?;
            assigned[i].push(row);
        }
    }
    let union = Set::new((0..domain.size()).filter(|&row| in_union[row]));
    Ok((union, assigned.into_iter().map(Set::new).collect()))
}

/// A set `Tᵢ` of at most `N / SMALL` rows is small: below that, a product tree on its rows is
/// faster than FFTs on the whole domain.
const SMALL: usize = 64;

/// The `qᵢ` with FFTs on the whole domain `H`. With `Q = P_{H∖V}`, `Fᵢ` is the polynomial of degree
/// `< N` equal to `Q` on the rows of `Aᵢ` and to `0` on the other rows of `H`: `Fᵢ = Q · Gᵢ`, as
/// both have degree `< N` and agree on `H`, so `qᵢ = Fᵢ / (Q · P_{Dᵢ})`.
fn on_domain(
    domain: &Domain,
    union: &Set,
    assigned: &[Set],
    polynomials: &[DensePolynomial<Fr>],
) -> Result<Vec<DensePolynomial<Fr>>, Error> {
    let n = domain.size();
    let q = Set::new((0..n).filter(|row| union.rows().binary_search(row).is_err()))
        .characteristic(domain)?;
    let q_evals = domain.fft(&q.coeffs);
    let sets: Vec<_> = assigned.iter().zip(polynomials).collect();
    in_batches(&sets, |&(a, p)| {
        let mut f = vec![Fr::zero(); n];
        for &row in a.rows() {
            f[row] = q_evals[row];
        }
        let f = DensePolynomial::from_coefficients_vec(domain.ifft(&f));
        divide_exact(&f, &(&q * p))
    })
}

/// The `qᵢ` on the rows of `Tᵢ = V ∖ Dᵢ ⊇ Aᵢ`. With the weights `wᵥ = 1 / P_V'(ωᵛ)`,
/// `Gᵢ = Σ_{v ∈ Aᵢ} wᵥ · P_V / (x − ωᵛ)`, and `P_V = P_{Dᵢ} · P_{Tᵢ}`, so
/// `qᵢ = P_{Tᵢ ∖ Aᵢ} · Σ_{v ∈ Aᵢ} wᵥ · P_{Aᵢ} / (x − ωᵛ)`.
fn on_rows(
    domain: &Domain,
    union: &Set,
    assigned: &[Set],
    sets: &[Set],
) -> Result<Vec<DensePolynomial<Fr>>, Error> {
    // wᵥ = 1 / P_V'(ωᵛ), from the values of the derivative on the domain.
    let p_v = union.characteristic(domain)?;
    let derivative: Vec<Fr> = p_v
        .coeffs
        .iter()
        .enumerate()
        .skip(1)
        .map(|(k, c)| *c * Fr::from(k as u64))
        .collect();
    let derivative = domain.fft(&derivative);
    let mut weights: Vec<Fr> = union.rows().iter().map(|&row| derivative[row]).collect();
    batch_inversion(&mut weights);

    let sets: Vec<_> = assigned.iter().zip(sets).collect();
    in_batches(&sets, |&(a, d)| {
        let points: Vec<(Fr, Fr)> = a
            .rows()
            .iter()
            .filter_map(|row| {
                let i = union.rows().binary_search(row).ok()?;
                Some((domain.element(*row), weights[i]))
            })
            .collect();
        let (numerator, _) = sum_of_fractions(&points);
        let rest = Set::new(union.rows().iter().copied().filter(|row| {
            d.rows().binary_search(row).is_err() && a.rows().binary_search(row).is_err()
        }));
        Ok(&numerator * &rest.characteristic(domain)?)
    })
}

/// `Σ wᵥ / (x − rᵥ)` over `points` `(rᵥ, wᵥ)`, as `(numerator, ∏ (x − rᵥ))`, by a product tree.
fn sum_of_fractions(points: &[(Fr, Fr)]) -> (DensePolynomial<Fr>, DensePolynomial<Fr>) {
    match points {
        [] => (
            DensePolynomial::zero(),
            DensePolynomial::from_coefficients_vec(vec![Fr::ONE]),
        ),
        [(r, w)] => (
            DensePolynomial::from_coefficients_vec(vec![*w]),
            DensePolynomial::from_coefficients_vec(vec![-*r, Fr::ONE]),
        ),
        _ => {
            let (left, right) = points.split_at(points.len() / 2);
            let ((n1, d1), (n2, d2)) = (sum_of_fractions(left), sum_of_fractions(right));
            (&(&n1 * &d2) + &(&n2 * &d1), &d1 * &d2)
        }
    }
}

/// The most sets the prover works on at once. The work on each set is parallel inside, and a rayon
/// thread waiting for it runs the work on other sets on top of its own stack: with all the sets at
/// once, a few hundred of them overflow the 2 MiB stack of a rayon thread.
const BATCH: usize = 8;

/// `f` on every item, in parallel batches of [`BATCH`] items.
fn in_batches<T: Sync, U: Send>(
    items: &[T],
    f: impl Fn(&T) -> Result<U, Error> + Sync,
) -> Result<Vec<U>, Error> {
    let mut results = Vec::with_capacity(items.len());
    for batch in items.chunks(BATCH) {
        results.extend(batch.par_iter().map(&f).collect::<Result<Vec<_>, _>>()?);
    }
    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn computes_the_same_coefficients_both_ways() {
        let domain = Domain::new(64).unwrap();
        let set = |rows: &mut dyn Iterator<Item = usize>| Set::new(rows.collect::<Vec<_>>());
        let cases: Vec<Vec<Set>> = vec![
            vec![
                set(&mut [0, 1, 9].into_iter()),
                set(&mut [1, 4, 9, 20].into_iter()),
                set(&mut [5, 15].into_iter()),
            ],
            // Two halves, and odd and even rows: the rows of `V` cover the domain.
            vec![set(&mut (0..40)), set(&mut (40..64))],
            vec![set(&mut (0..64).step_by(2)), set(&mut (1..64).step_by(2))],
            // Each set misses one row, and each misses the rows of one residue.
            (0..64)
                .map(|r| set(&mut (0..64).filter(move |x| *x != r)))
                .collect(),
            (0..16)
                .map(|g| set(&mut (0..64).filter(move |x| x % 16 != g)))
                .collect(),
        ];
        for sets in cases {
            let polynomials: Vec<_> = sets
                .iter()
                .map(|s| s.characteristic(&domain).unwrap())
                .collect();
            let (union, assigned) = assign(&domain, &sets, "test").unwrap();
            let rows = on_rows(&domain, &union, &assigned, &sets).unwrap();
            let whole = on_domain(&domain, &union, &assigned, &polynomials).unwrap();
            assert_eq!(rows, whole);
            let sum = rows
                .iter()
                .zip(&polynomials)
                .fold(DensePolynomial::zero(), |sum, (q, p)| &sum + &(q * p));
            assert_eq!(sum, DensePolynomial::from_coefficients_vec(vec![Fr::ONE]));
        }
    }
}
