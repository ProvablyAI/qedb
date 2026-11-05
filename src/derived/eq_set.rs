//! Positions where two slices are equal, `X̃₀ = eqSet(ũ, ṽ)` (Table 2).
//!
//! `X₀` is the set of rows of `∗` where `u` and `v` are equal. The test takes `Δ = u − v`, which
//! the verifier computes from the handles; the pre-image check `X̃_α = α⁻¹(ṽ)` is the same test
//! with `Δ = v − α·1`.
//!
//! The prover sends `X₊ = {j : Δⱼ > 0}`, `X₋ = {j : Δⱼ < 0}` and `C = X₊ ∪ X₋`, and the verifier
//! checks
//!
//! 1. `X₀`, `X₊`, `X₋` partition `∗`, with two complement tests: `C = ∗ ∖ X₀`, and `X₋ = C ∖ X₊`,
//!    i.e. `P_{X₊} · P_{X₋} = P_C`;
//! 2. the zero test `Δ[X₀] = 0`;
//! 3. one sign check of `(Δ − 1)[X₊] ≥ 0` and `(−Δ − 1)[X₋] ≥ 0`: `Δ > 0` on `X₊` and `Δ < 0` on
//!    `X₋`, for integers in `(−2^ℓ, 2^ℓ]`.

use super::sign_check::SignCheckProof;
use crate::Error;
use crate::basic::complement::ComplementProof;
use crate::basic::zero_test::ZeroTestProof;
use crate::handle::{
    CommittedSet, CommittedSlice, Set, SetHandle, SliceHandle, Universe, UniverseHandle,
};
use crate::setup::Srs;
use crate::transcript::Transcript;
use ark_bls12_381::Fr;
use ark_ff::{PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Proof that a set is the set of rows where a slice is zero.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct EqSetProof {
    /// `X₊`.
    pub(crate) greater: SetHandle,
    /// `X₋`.
    pub(crate) less: SetHandle,
    /// `C = X₊ ∪ X₋`.
    pub(crate) different: SetHandle,
    /// `C = ∗ ∖ X₀`.
    pub(crate) complement: ComplementProof,
    /// `X₋ = C ∖ X₊`.
    pub(crate) split: ComplementProof,
    /// `Δ[X₀] = 0`.
    pub(crate) zero_test: ZeroTestProof,
    /// `(Δ − 1)[X₊] ≥ 0` and `(−Δ − 1)[X₋] ≥ 0`.
    pub(crate) sign_check: SignCheckProof,
}

impl EqSetProof {
    /// Proves that `X₀` is the set of rows of `universe` where `Δ` is zero, with the other values
    /// in `(−2^ℓ, 2^ℓ]`.
    pub fn prove(
        srs: &Srs,
        universe: &Universe,
        delta: &CommittedSlice,
        x0: &CommittedSet,
        ell: usize,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let values = delta.slice().values();
        let (mut zero, mut greater, mut less) = (vec![], vec![], vec![]);
        for &row in universe.rows().set().rows() {
            let value = values.get(row).copied().unwrap_or_default();
            if value.is_zero() {
                zero.push(row);
            } else if value.into_bigint() <= Fr::MODULUS_MINUS_ONE_DIV_TWO {
                greater.push(row);
            } else {
                less.push(row);
            }
        }
        if Set::new(zero) != *x0.set() {
            return Err(Error::InvalidWitness("eqSet"));
        }
        let greater = Set::new(greater).commit(srs)?;
        let less = Set::new(less).commit(srs)?;
        let different = universe.rows().set().difference(x0.set()).commit(srs)?;
        let witness = |error| match error {
            Error::InvalidWitness(_) => Error::InvalidWitness("eqSet"),
            error => error,
        };
        let ones = universe.ones();

        Ok(Self {
            greater: greater.handle(),
            less: less.handle(),
            different: different.handle(),
            complement: ComplementProof::prove(srs, universe.rows(), x0, &different, transcript)
                .map_err(witness)?,
            split: ComplementProof::prove(srs, &different, &greater, &less, transcript)
                .map_err(witness)?,
            zero_test: ZeroTestProof::prove(srs, delta, x0, transcript).map_err(witness)?,
            sign_check: SignCheckProof::prove(
                srs,
                &[(&(delta - ones), &greater), (&(&-delta - ones), &less)],
                ell,
                transcript,
            )
            .map_err(witness)?,
        })
    }

    /// Verifies that `X₀` is the set of rows of `universe` where the slice `Δ` is zero.
    pub fn verify(
        &self,
        srs: &Srs,
        universe: UniverseHandle,
        delta: SliceHandle,
        x0: SetHandle,
        ell: usize,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        let parts = [
            (delta - universe.ones, self.greater),
            (-delta - universe.ones, self.less),
        ];
        self.complement
            .verify(universe.rows, x0, self.different, transcript)
            .and_then(|()| {
                self.split
                    .verify(self.different, self.greater, self.less, transcript)
            })
            .and_then(|()| self.zero_test.verify(delta, x0, transcript))
            .and_then(|()| self.sign_check.verify(srs, &parts, ell, transcript))
            .map_err(|_| Error::Rejected("eqSet"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handle::Slice;
    use ark_std::test_rng;

    const ELL: usize = 8;
    // Δ on 12 rows: zero on 0, 3, 6, 7, 11; positive on 1, 4, 8, 10; negative on 2, 5, 9.
    const DELTA: [i64; 12] = [0, 3, -2, 0, 5, -1, 0, 0, 7, -4, 1, 0];
    const ZERO: [usize; 5] = [0, 3, 6, 7, 11];
    const GREATER: [usize; 4] = [1, 4, 8, 10];
    const LESS: [usize; 3] = [2, 5, 9];

    struct Setup {
        srs: Srs,
        universe: Universe,
    }

    fn setup() -> Setup {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let universe = Universe::new(&srs, 12).unwrap();
        Setup { srs, universe }
    }

    fn slice(srs: &Srs, values: &[i64]) -> CommittedSlice {
        Slice::new(values.iter().map(|&x| Fr::from(x)).collect())
            .commit(srs)
            .unwrap()
    }

    fn set(srs: &Srs, rows: impl IntoIterator<Item = usize>) -> CommittedSet {
        Set::new(rows).commit(srs).unwrap()
    }

    fn prove(s: &Setup, delta: &CommittedSlice, x0: &CommittedSet) -> Result<EqSetProof, Error> {
        let transcript = &mut Transcript::new("test");
        EqSetProof::prove(&s.srs, &s.universe, delta, x0, ELL, transcript)
    }

    fn verify(
        proof: &EqSetProof,
        s: &Setup,
        delta: &CommittedSlice,
        x0: &CommittedSet,
    ) -> Result<(), Error> {
        let transcript = &mut Transcript::new("test");
        proof.verify(
            &s.srs,
            s.universe.handle(),
            delta.handle(),
            x0.handle(),
            ELL,
            transcript,
        )
    }

    #[test]
    fn accepts_the_rows_where_the_slice_is_zero() {
        let s = setup();
        let cases: [(&[i64], Vec<usize>); 3] = [
            (&DELTA, ZERO.to_vec()),
            (&[], (0..12).collect()),
            (&[1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6], vec![]),
        ];

        for (values, zero) in cases {
            let (delta, x0) = (slice(&s.srs, values), set(&s.srs, zero));
            let proof = prove(&s, &delta, &x0).unwrap();
            assert_eq!(verify(&proof, &s, &delta, &x0), Ok(()));
        }
        // A wrong X₀.
        let delta = slice(&s.srs, &DELTA);
        assert_eq!(
            prove(&s, &delta, &set(&s.srs, [0, 3])),
            Err(Error::InvalidWitness("eqSet"))
        );
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Broken {
        Complement,
        Split,
        ZeroTest,
        SignCheck,
    }

    /// A proof with the given sets, honest except for `broken`, which is taken from `honest`.
    /// Every sub-proof is made on the verifier's transcript of the previous ones.
    fn forge(
        s: &Setup,
        honest: &EqSetProof,
        delta: &CommittedSlice,
        [x0, different, greater, less]: [&CommittedSet; 4],
        broken: Broken,
    ) -> EqSetProof {
        let transcript = &mut Transcript::new("test");
        let (srs, rows, ones) = (&s.srs, s.universe.rows(), s.universe.ones());

        let complement = if broken == Broken::Complement {
            let _ = honest.complement.verify(
                rows.handle(),
                x0.handle(),
                different.handle(),
                transcript,
            );
            honest.complement
        } else {
            ComplementProof::prove(srs, rows, x0, different, transcript).unwrap()
        };
        let split = if broken == Broken::Split {
            let _ = honest.split.verify(
                different.handle(),
                greater.handle(),
                less.handle(),
                transcript,
            );
            honest.split
        } else {
            ComplementProof::prove(srs, different, greater, less, transcript).unwrap()
        };
        let zero_test = if broken == Broken::ZeroTest {
            let _ = honest
                .zero_test
                .verify(delta.handle(), x0.handle(), transcript);
            honest.zero_test
        } else {
            ZeroTestProof::prove(srs, delta, x0, transcript).unwrap()
        };
        let sign_check = if broken == Broken::SignCheck {
            let parts = [
                (delta.handle() - ones.handle(), greater.handle()),
                (-delta.handle() - ones.handle(), less.handle()),
            ];
            let _ = honest.sign_check.verify(srs, &parts, ELL, transcript);
            honest.sign_check.clone()
        } else {
            let parts = [(&(delta - ones), greater), (&(&-delta - ones), less)];
            SignCheckProof::prove(srs, &parts, ELL, transcript).unwrap()
        };

        EqSetProof {
            greater: greater.handle(),
            less: less.handle(),
            different: different.handle(),
            complement,
            split,
            zero_test,
            sign_check,
        }
    }

    #[test]
    fn each_check_is_needed() {
        let s = setup();
        let delta = slice(&s.srs, &DELTA);
        let honest = prove(&s, &delta, &set(&s.srs, ZERO)).unwrap();
        let without =
            |sets: &[usize], row: usize| set(&s.srs, sets.iter().copied().filter(|&r| r != row));
        let with = |sets: &[usize], row: usize| set(&s.srs, sets.iter().copied().chain([row]));
        let different: Vec<usize> = GREATER.iter().chain(&LESS).copied().collect();
        let (greater, less) = (set(&s.srs, GREATER), set(&s.srs, LESS));
        let reject = Err(Error::Rejected("eqSet"));

        // Row 6 (Δ₆ = 0) left out of X₀ and of C: only the complement test catches it.
        let x0 = without(&ZERO, 6);
        let sets = [&x0, &set(&s.srs, different.clone()), &greater, &less];
        let forged = forge(&s, &honest, &delta, sets, Broken::Complement);
        assert_eq!(verify(&forged, &s, &delta, &x0), reject);

        // Row 6 moved to C but to neither X₊ nor X₋: only the split catches it.
        let c = with(&different, 6);
        let forged = forge(
            &s,
            &honest,
            &delta,
            [&x0, &c, &greater, &less],
            Broken::Split,
        );
        assert_eq!(verify(&forged, &s, &delta, &x0), reject);

        // Row 1 (Δ₁ = 3) claimed in X₀: only the zero test catches it.
        let x0_extra = with(&ZERO, 1);
        let sets = [
            &x0_extra,
            &without(&different, 1),
            &without(&GREATER, 1),
            &less,
        ];
        let forged = forge(&s, &honest, &delta, sets, Broken::ZeroTest);
        assert_eq!(verify(&forged, &s, &delta, &x0_extra), reject);

        // Row 6 (Δ₆ = 0) claimed in X₊: only the sign check catches it.
        let sets = [&x0, &c, &with(&GREATER, 6), &less];
        let forged = forge(&s, &honest, &delta, sets, Broken::SignCheck);
        assert_eq!(verify(&forged, &s, &delta, &x0), reject);
    }
}
