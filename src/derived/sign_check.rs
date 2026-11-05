//! Sign check within target subsets (Table 2): `ṽⱼ[X̃ⱼ] ≥ 0` for every `j`, i.e. every value of
//! `vⱼ` on the rows of `Xⱼ` is an integer in `[0, 2^ℓ)`.
//!
//! The prover sends a slice `R` equal to `vⱼ` on `Xⱼ` (and to `0` on the other rows), and the
//! verifier checks
//!
//! 1. the zero test `(R − vⱼ)[Xⱼ] = 0` for every `j`;
//! 2. the range check `R ∈ [0, 2^ℓ)`.
//!
//! Compared with the paper:
//!
//! - The paper builds `R` with a nullifying test, which also proves `R = 0` outside the subsets.
//!   Here only `R = vⱼ` on `Xⱼ` is proved (one zero test, no complement): the conclusion is about
//!   the rows of `Xⱼ`, where `vⱼ = R ≥ 0`, so the values of `R` on the other rows do not matter.
//!   The honest prover sets them to `0`, which passes the range check.
//! - One `R` and one range check serve all the subsets.
//! - The verifier does not check that the subsets are disjoint: on a row in two subsets, the zero
//!   tests force `R` to equal both slices, so both are non-negative there.
//!
//! A strict check `v[X] > 0` is `(v − 1)[X] ≥ 0` for integers, with `1` the all-ones slice of the
//! universe.

use super::range_check::RangeCheckProof;
use crate::Error;
use crate::basic::zero_test::ZeroTestProof;
use crate::handle::{CommittedSet, CommittedSlice, SetHandle, Slice, SliceHandle};
use crate::setup::Srs;
use crate::transcript::Transcript;
use ark_bls12_381::Fr;
use ark_ff::Zero;
use ark_poly::EvaluationDomain;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Proof that slices are non-negative on sets.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct SignCheckProof {
    /// `R`, equal to `vⱼ` on `Xⱼ`.
    pub(crate) remainder: SliceHandle,
    /// `(R − vⱼ)[Xⱼ] = 0`, one per subset.
    pub(crate) zero_tests: Vec<ZeroTestProof>,
    /// `R ∈ [0, 2^ℓ)`.
    pub(crate) range_check: RangeCheckProof,
}

impl SignCheckProof {
    /// Proves `vⱼ[Xⱼ] ≥ 0` for the pairs `(vⱼ, Xⱼ)` in `parts`, with values in `[0, 2^ℓ)`.
    pub fn prove(
        srs: &Srs,
        parts: &[(&CommittedSlice, &CommittedSet)],
        ell: usize,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let mut values = vec![Fr::zero(); srs.domain().size()];
        for (v, x) in parts {
            let v = v.slice().values();
            for &row in x.set().rows() {
                values[row] = v.get(row).copied().unwrap_or_default();
            }
        }
        let remainder = Slice::new(values).commit(srs)?;
        let witness = |error| match error {
            Error::InvalidWitness(_) => Error::InvalidWitness("sign check"),
            error => error,
        };

        let zero_tests = parts
            .iter()
            .map(|(v, x)| ZeroTestProof::prove(srs, &(&remainder - v), x, transcript))
            .collect::<Result<_, _>>()
            .map_err(witness)?;
        let range_check =
            RangeCheckProof::prove(srs, &remainder, ell, transcript).map_err(witness)?;
        Ok(Self {
            remainder: remainder.handle(),
            zero_tests,
            range_check,
        })
    }

    /// Verifies `vⱼ[Xⱼ] ≥ 0` for the pairs of handles in `parts`, with values in `[0, 2^ℓ)`.
    pub fn verify(
        &self,
        srs: &Srs,
        parts: &[(SliceHandle, SetHandle)],
        ell: usize,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        let reject = || Error::Rejected("sign check");
        if self.zero_tests.len() != parts.len() {
            return Err(reject());
        }
        for ((v, x), zero_test) in parts.iter().zip(&self.zero_tests) {
            zero_test
                .verify(self.remainder - *v, *x, transcript)
                .map_err(|_| reject())?;
        }
        self.range_check
            .verify(srs, self.remainder, ell, transcript)
            .map_err(|_| reject())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handle::{Set, Universe};
    use ark_ff::Field;
    use ark_std::test_rng;

    const ELL: usize = 8;

    struct Setup {
        srs: Srs,
        universe: Universe,
        v: CommittedSlice,
    }

    // 12 rows in a domain of 16; vⱼ = j − 4: negative on rows 0–3, zero on row 4.
    fn setup() -> Setup {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let universe = Universe::new(&srs, 12).unwrap();
        let v = slice(&srs, |j| Fr::from(j as u64) - Fr::from(4u64));
        Setup { srs, universe, v }
    }

    fn slice(srs: &Srs, value: impl Fn(usize) -> Fr) -> CommittedSlice {
        Slice::new((0..12).map(value).collect())
            .commit(srs)
            .unwrap()
    }

    fn set(srs: &Srs, rows: &[usize]) -> CommittedSet {
        Set::new(rows.iter().copied()).commit(srs).unwrap()
    }

    fn prove(
        s: &Setup,
        parts: &[(&CommittedSlice, &CommittedSet)],
    ) -> Result<SignCheckProof, Error> {
        SignCheckProof::prove(&s.srs, parts, ELL, &mut Transcript::new("test"))
    }

    fn verify(
        proof: &SignCheckProof,
        s: &Setup,
        parts: &[(&CommittedSlice, &CommittedSet)],
    ) -> Result<(), Error> {
        let parts: Vec<_> = parts
            .iter()
            .map(|(v, x)| (v.handle(), x.handle()))
            .collect();
        proof.verify(&s.srs, &parts, ELL, &mut Transcript::new("test"))
    }

    /// A proof with the given remainder and zero tests, and a range check of `range_of` made on
    /// the verifier's transcript after those zero tests.
    fn forge(
        s: &Setup,
        parts: &[(&CommittedSlice, &CommittedSet)],
        remainder: &CommittedSlice,
        zero_tests: Vec<ZeroTestProof>,
        range_of: &CommittedSlice,
    ) -> SignCheckProof {
        let transcript = &mut Transcript::new("test");
        for ((v, x), zero_test) in parts.iter().zip(&zero_tests) {
            let _ = zero_test.verify(remainder.handle() - v.handle(), x.handle(), transcript);
        }
        SignCheckProof {
            remainder: remainder.handle(),
            zero_tests,
            range_check: RangeCheckProof::prove(&s.srs, range_of, ELL, transcript).unwrap(),
        }
    }

    fn zero_test(s: &Setup, v: &CommittedSlice, x: &CommittedSet) -> ZeroTestProof {
        ZeroTestProof::prove(&s.srs, v, x, &mut Transcript::new("test")).unwrap()
    }

    #[test]
    fn accepts_signs() {
        let s = setup();
        // v > 0 as (v − 1) ≥ 0, and v < 0 as (−v − 1) ≥ 0.
        let strict = &s.v - s.universe.ones();
        let negated = slice(&s.srs, |j| Fr::from(3u64) - Fr::from(j as u64));
        let (at_least_0, above_0, below_0) = (
            set(&s.srs, &[4, 7, 11]),
            set(&s.srs, &[5, 9]),
            set(&s.srs, &[0, 3]),
        );

        let cases: [&[(&CommittedSlice, &CommittedSet)]; 4] = [
            &[(&s.v, &at_least_0)],
            &[(&strict, &above_0)],
            &[(&strict, &above_0), (&negated, &below_0)],
            &[(&s.v, &set(&s.srs, &[]))],
        ];
        for parts in cases {
            let proof = prove(&s, parts).unwrap();
            assert_eq!(verify(&proof, &s, parts), Ok(()));
        }
        // v is 0 on row 4: not strictly positive.
        assert_eq!(
            prove(&s, &[(&strict, &at_least_0)]),
            Err(Error::InvalidWitness("sign check"))
        );
    }

    #[test]
    fn each_check_is_needed() {
        let s = setup();
        let reject = Err(Error::Rejected("sign check"));
        // v₂ = −2 < 0 and v₅ = 1.
        let x = set(&s.srs, &[2, 5]);
        let parts = [(&s.v, &x)];

        // 1. R = 0 on row 2 instead of v₂: only the zero test catches it.
        let r = slice(&s.srs, |j| Fr::from(u64::from(j == 5)));
        let other = zero_test(&s, &(&r - &s.v), &set(&s.srs, &[5]));
        let forged = forge(&s, &parts, &r, vec![other], &r);
        assert_eq!(verify(&forged, &s, &parts), reject);

        // 2. R = v on X, negative on row 2, with the range check of another slice: only the
        //    range check catches it.
        let r = slice(&s.srs, |j| match j {
            2 => -Fr::from(2u64),
            5 => Fr::ONE,
            _ => Fr::zero(),
        });
        let honest = zero_test(&s, &(&r - &s.v), &x);
        let in_range = slice(&s.srs, |_| Fr::ONE);
        let forged = forge(&s, &parts, &r, vec![honest], &in_range);
        assert_eq!(verify(&forged, &s, &parts), reject);

        // 3. Two subsets and a single zero test: R = v on {5} only, so the subset {2} is never
        //    tested. Only the count of zero tests catches it.
        let (five, two) = (set(&s.srs, &[5]), set(&s.srs, &[2]));
        let parts = [(&s.v, &five), (&s.v, &two)];
        let r = slice(&s.srs, |j| Fr::from(u64::from(j == 5)));
        let honest = zero_test(&s, &(&r - &s.v), &five);
        let forged = forge(&s, &parts, &r, vec![honest], &r);
        assert_eq!(verify(&forged, &s, &parts), reject);
    }
}
