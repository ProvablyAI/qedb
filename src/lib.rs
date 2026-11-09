//! Primitives of qedb ([ePrint 2025/1408](https://eprint.iacr.org/2025/1408)), over BLS12-381.
//!
//! The paper describes verifiable databases in an idealized model where the prover sends
//! *handles* to sets and to vectors (slices), and the verifier runs a small set of tests on them.
//! This crate implements that model with KZG commitments:
//!
//! - [`setup`]: the structured reference string ([`setup::Srs`]) and the [`setup::VerifierKey`];
//! - [`handle`]: sets of rows and slices of values, as held by the prover ([`handle::Set`],
//!   [`handle::Slice`]), and their handles, as seen by the verifier ([`handle::SetHandle`],
//!   [`handle::SliceHandle`]). Slice handles are homomorphic;
//! - [`basic`]: the basic tests of Fig. 8: subset, complement, intersection, union, zero test,
//!   inner product, and read;
//! - [`derived`]: the derived tests of Table 2: nullifying test, range check, sign check, positions
//!   where two slices are equal (and the pre-image check), and sum check;
//! - [`transcript`]: the Fiat–Shamir transcript shared by all the tests of a proof.
//!
//! Every test has a `prove`, run by the prover on committed sets and slices, and a `verify`, run
//! by the verifier on handles. Both take the same [`transcript::Transcript`]: a test appends its
//! inputs and its proof before drawing a challenge, so a query is proved by calling the tests in
//! the same order on both sides. SQL operators (App. E) are compositions of the tests, as in the
//! `transactions` benchmark.
//!
//! # Differences from the paper
//!
//! The tests prove the same statements as the paper's, with these constructions:
//!
//! - set relations are checked with pairing equations on the accumulators, and the equations of a
//!   test are batched with powers of a challenge into one multi-pairing;
//! - the union `W = S₁ ∪ … ∪ Sₖ` is proved with complements within `W` instead of within all
//!   rows: `Sᵢ ⊆ W` and the `W ∖ Sᵢ` have no common row;
//! - `read` binds the answer to the set with one opening at a challenge, and a zero test;
//! - the range check uses bit polynomials and one quotient by the vanishing polynomial, instead of
//!   bit slices and nullifying tests;
//! - a sign check proves the slice equal to the target on the subset only, proves strict signs
//!   from integrality, and serves several subsets with one range check.
//!
//! # Example
//!
//! The sum of a column on a set of rows, as in `SELECT SUM(col) … WHERE …`:
//!
//! ```
//! use ark_bls12_381::Fr;
//! use ark_std::test_rng;
//! use qedb_primitives::derived::sum_check::SumCheckProof;
//! use qedb_primitives::handle::{Set, Slice};
//! use qedb_primitives::setup::Srs;
//! use qedb_primitives::transcript::Transcript;
//!
//! # fn main() -> Result<(), qedb_primitives::Error> {
//! // Setup and preprocessing: a table of 4 rows with one column.
//! let srs = Srs::setup(4, &mut test_rng())?;
//! let column = Slice::new([10u64, 20, 30, 40].map(Fr::from).to_vec()).commit(&srs)?;
//!
//! // The prover: the rows selected by the query, and the sum on them.
//! let rows = Set::new([1, 3]).commit(&srs)?;
//! let sum = Fr::from(60u64);
//! let transcript = &mut Transcript::new("example");
//! let proof = SumCheckProof::prove(&srs, &column, &rows, sum, transcript)?;
//!
//! // The verifier: the verifier key and the handles only.
//! let vk = srs.verifier_key();
//! let (column, rows) = (column.handle(), rows.handle());
//! let transcript = &mut Transcript::new("example");
//! proof.verify(&vk, column, rows, sum, transcript)?;
//! # Ok(())
//! # }
//! ```

#![warn(missing_docs)]

pub mod basic;
pub mod derived;
mod error;
pub mod handle;
pub mod setup;
pub mod transcript;

pub use error::Error;
