# Changelog

All notable changes to this project are documented in this file. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project follows
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2026-11-05

First release: the primitives of qedb ([ePrint 2025/1408](https://eprint.iacr.org/2025/1408)).

### Added

- `setup`: the structured reference string `Srs`, with `commit_g1` and `commit_g2`, and the `VerifierKey`.
- `handle`: `Set` and `Slice`, committed as `CommittedSet` and `CommittedSlice`; their handles `SetHandle` and `SliceHandle`, with the homomorphism `α·u + w`; the `Universe` of a table (its rows and the all-ones slice) and its `UniverseHandle`.
- `transcript`: the Fiat–Shamir `Transcript`.
- `basic`: the tests of Fig. 8: `SubsetProof`, `ComplementProof`, `IntersectionProof`, `UnionProof`, `ZeroTestProof`, `InnerProductProof` and `ReadProof`.
- `derived`: the tests of Table 2: `NullifyingProof`, `RangeCheckProof` (with the number of bits `ℓ` as a parameter), `SignCheckProof`, `EqSetProof` (positions where two slices are equal, and the pre-image check) and `SumCheckProof`.
- `Error`.
- The `transactions` benchmark: the paper's queries `QTot`, `QCntTx` and `QMatch`, composed from the tests.
- CI: formatting, clippy, tests and documentation, on pushes to `main` and on pull requests.
