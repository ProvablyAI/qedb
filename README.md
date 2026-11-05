# qedb: Expressive and Modular Verifiable Databases (without SNARKs)

Which is a recursive acronym standing for ***q***edb ***e***rror-checks ***d***ata***b***ases.
It is also a shameless pun on it being a ***proof*** system for DBs.

A verifiable database lets a client check the answer to a query without trusting the server
that runs it: with the answer comes a short proof, which the client verifies against a small
digest of the database. ***qedb*** is such a scheme for a subset of SQL, built on pairings and
without general-purpose SNARKs. It is described in the paper
[qedb: Expressive and Modular Verifiable Databases (without SNARKs)](https://eprint.iacr.org/2025/1408).

This crate implements the paper's **primitives**: the tests that queries are built from. Turning
SQL into these tests is up to the application; the benchmark shows how for three example queries.

## How it works

The paper describes the database with two kinds of objects:

- **sets of rows**, such as the rows where `country = 'IT'`;
- **slices**, the values of a column, or of a combination of columns, on the rows.

The verifier only holds short *handles* to them: KZG commitments over BLS12-381. The prover
convinces the verifier of facts about the sets and slices behind the handles with **tests**:

| Module | Contents |
|---|---|
| `setup` | the structured reference string `Srs`, and the `VerifierKey` the verifier needs |
| `handle` | `Set`, `Slice` and their handles; slice handles add up and scale, so the verifier computes `2·u − v` itself |
| `basic` | the basic tests (Fig. 8): subset, complement, intersection, union, zero test, inner product, read |
| `derived` | the derived tests (Table 2): nullifying test, range check, sign check, equal positions, sum check |
| `transcript` | the Fiat–Shamir transcript that makes a sequence of tests non-interactive |

A query is a sequence of tests. For example, `SELECT SUM(price) … WHERE …` is a sum check of the
`price` slice on the set of selected rows.

## Example

```rust
use ark_bls12_381::Fr;
use ark_std::test_rng;
use qedb::derived::sum_check::SumCheckProof;
use qedb::handle::{Set, Slice, Universe};
use qedb::setup::Srs;
use qedb::transcript::Transcript;

// Setup and preprocessing: a table of 4 rows with one column.
let srs = Srs::setup(4, &mut test_rng())?;
let universe = Universe::new(&srs, 4)?;
let column = Slice::new([10u64, 20, 30, 40].map(Fr::from).to_vec()).commit(&srs)?;

// The prover: the selected rows 1 and 3, and the sum of the column on them.
let rows = Set::new([1, 3]).commit(&srs)?;
let proof = SumCheckProof::prove(&srs, &universe, &column, &rows, Fr::from(60u64),
    &mut Transcript::new("example"))?;

// The verifier: only the verifier key and the handles.
let (universe, column, rows) = (universe.handle(), column.handle(), rows.handle());
proof.verify(&srs.verifier_key(), universe, column, rows, Fr::from(60u64),
    &mut Transcript::new("example"))?;
```

The prover and the verifier run the tests in the same order on a transcript with the same label.
The full example is in the crate documentation (`cargo doc --open`).

## Differences from the paper

The tests prove the same statements as the paper's, with faster constructions:

- the equations of a test are batched with powers of a random challenge into one multi-pairing;
- the union `W = S₁ ∪ … ∪ Sₖ` uses complements within `W` rather than within all the rows;
- `read` binds the answer to the set with one opening at a random point and a zero test;
- the range check uses bit polynomials and one quotient, rather than bit slices and nullifying
  tests;
- a sign check proves the slice equal to the target only on its subset, proves strict signs
  from integrality, and serves several subsets with one range check.

## Benchmark

`benches/transactions.rs` proves the paper's three queries on a generated `Transaction` table:

- `QTot`: `SELECT SUM(price) … WHERE account_id = 5938 AND trade_date = '2025-01-01'`;
- `QCntTx`: `SELECT COUNT(*) … WHERE trade_date BETWEEN '2025-01-01' AND '2025-03-31'`;
- `QMatch`: `SELECT tx_id, price, expected_price, price = expected_price … WHERE trade_date = '2025-04-05'`.

```bash
make bench                                     # 2^10 to 2^16 rows
QEDB_LOG_ROWS=17 cargo bench --bench transactions
```

On an Apple M3 Pro (11 cores):

| Rows | Query | Prove | Verify | Proof |
|---|---|---|---|---|
| 2^16 | `QTot` | 0.62 s | 6.5 ms | 1,120 B |
| 2^16 | `QCntTx` | 4.46 s | 15.1 ms | 7,248 B |
| 2^16 | `QMatch` (171 rows) | 0.83 s | 7.2 ms | 720 B |
| 2^17 | `QTot` | 1.26 s | 6.5 ms | 1,120 B |
| 2^17 | `QCntTx` | 8.37 s | 14.5 ms | 7,248 B |
| 2^17 | `QMatch` (365 rows) | 1.53 s | 7.3 ms | 720 B |

The verifier key is 524 bytes, and proof sizes do not depend on the number of rows.

## Development

```bash
make check   # what CI runs: formatting, clippy, tests and documentation
```

The toolchain (Rust 1.97) is pinned in `rust-toolchain.toml`. See
[CONTRIBUTING.md](CONTRIBUTING.md) to contribute.

## Security

- The code has not been audited.
- `Srs::setup` samples the secret `τ` itself, so whoever runs it can forge proofs: use it for
  tests and benchmarks. In production the powers of `τ` must come from a trusted-setup ceremony.
- The range and sign checks prove that values are integers in `[0, 2^ℓ)`, with `ℓ` chosen by
  the caller (at most 254).

## License

This project is licensed under the [Business Source License 1.1](LICENSE.md).

- Copyright © 2026 Provably Technologies LTD
- You may not offer the Software as a commercial hosted service without purchasing a commercial
  license from [Provably Technologies Ltd](https://provably.ai).

See the [LICENSE](LICENSE.md) file for full terms and details.
