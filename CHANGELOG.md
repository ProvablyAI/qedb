# Changelog

All notable changes to this project are documented in this file. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project follows
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- `Srs::lagrange`, the Lagrange basis `[λᵢ(τ)]₁`: computed from `τ` by `Srs::setup`, and from the
  powers by `Srs::from_powers` (once: about 12 s for 2^17 rows). `Srs::new` takes the powers and a
  stored basis.
- `Srs::commit_lagrange`, the commitment to a polynomial given by its values on the domain.

### Changed

- Slices and the range check's bits are committed in the Lagrange basis. Handles and proofs are
  unchanged; at 2^17 rows, `QCntTx` proves 41% faster and `QMatch` 32% faster.

## [0.1.0] - 2026-11-05

First release: the primitives of qedb ([ePrint 2025/1408](https://eprint.iacr.org/2025/1408)).

### Added

- `setup`: the structured reference string `Srs`, with `commit_g1` and `commit_g2`, `from_powers`
  to load existing powers, and the `VerifierKey`.
- `handle`: `Set` and `Slice`, committed as `CommittedSet` and `CommittedSlice`; their handles `SetHandle` and `SliceHandle`, with the homomorphism `α·u + w`; the `Universe` of a table (its rows and the all-ones slice) and its `UniverseHandle`.
- `transcript`: the Fiat–Shamir `Transcript`.
- `basic`: the tests of Fig. 8: `SubsetProof`, `ComplementProof`, `IntersectionProof`, `UnionProof`, `ZeroTestProof`, `InnerProductProof` and `ReadProof`.
- `derived`: the tests of Table 2: `NullifyingProof`, `RangeCheckProof` (with the number of bits `ℓ` as a parameter), `SignCheckProof`, `EqSetProof` (positions where two slices are equal, and the pre-image check) and `SumCheckProof`.
- `Error`.
- The `transactions` benchmark: the paper's queries `QTot`, `QCntTx` and `QMatch`, composed from the tests.
- CI: formatting, clippy, tests and documentation, on pushes to `main` and on pull requests.
