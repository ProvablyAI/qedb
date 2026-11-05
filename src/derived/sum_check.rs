//! Sum check within a target subset `Σ_{j ∈ X̃} ṽⱼ = y` (Table 2).
//!
//! The prover sends the indicator `u` of `X` and `X̄ = ∗ ∖ X`, and the verifier checks
//!
//! 1. the nullifying test `u = 1[X̄ → 0]`, whose complement of `X̄` must be the handle `X̃`: one
//!    complement test proves both `X̄ = ∗ ∖ X` and the nullifying test's complement;
//! 2. the inner product `⟨v, u⟩ = y`.
//!
//! With `v = 1`, `y` is the number of rows of `X`.

use super::nullifying::NullifyingProof;
use crate::Error;
use crate::basic::inner_product::InnerProductProof;
use crate::handle::{
    CommittedSet, CommittedSlice, SetHandle, Slice, SliceHandle, Universe, UniverseHandle,
};
use crate::setup::{Srs, VerifierKey};
use crate::transcript::Transcript;
use ark_bls12_381::Fr;
use ark_ff::{Field, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Proof of the sum of a slice on the rows of a set.
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct SumCheckProof {
    /// The indicator `u` of `X`.
    pub(crate) indicator: SliceHandle,
    /// `X̄ = ∗ ∖ X`.
    pub(crate) complement: SetHandle,
    /// `u = 1[X̄ → 0]`.
    pub(crate) nullifying: NullifyingProof,
    /// `⟨v, u⟩ = y`.
    pub(crate) inner_product: InnerProductProof,
}

impl SumCheckProof {
    /// Proves `Σ_{j ∈ X} vⱼ = y`, for `X` a subset of the rows of `universe`.
    pub fn prove(
        srs: &Srs,
        universe: &Universe,
        v: &CommittedSlice,
        x: &CommittedSet,
        y: Fr,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let rows = x.set().rows();
        let mut indicator = vec![Fr::zero(); rows.last().map_or(0, |row| row + 1)];
        for &row in rows {
            indicator[row] = Fr::ONE;
        }
        let indicator = Slice::new(indicator).commit(srs)?;
        let complement = universe.rows().set().difference(x.set()).commit(srs)?;
        let witness = |error| match error {
            Error::InvalidWitness(_) => Error::InvalidWitness("sum check"),
            error => error,
        };

        Ok(Self {
            indicator: indicator.handle(),
            complement: complement.handle(),
            nullifying: NullifyingProof::prove_with_complement(
                srs,
                universe,
                &indicator,
                universe.ones(),
                &complement,
                x,
                transcript,
            )
            .map_err(witness)?,
            inner_product: InnerProductProof::prove(srs, v, &indicator, y, transcript)
                .map_err(witness)?,
        })
    }

    /// Verifies `Σ_{j ∈ X} vⱼ = y` for the slice and set of the given handles.
    pub fn verify(
        &self,
        vk: &VerifierKey,
        universe: UniverseHandle,
        v: SliceHandle,
        x: SetHandle,
        y: Fr,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        if self.nullifying.complement != x {
            return Err(Error::Rejected("sum check"));
        }
        self.nullifying
            .verify(
                universe,
                self.indicator,
                universe.ones,
                self.complement,
                transcript,
            )
            .and_then(|()| {
                self.inner_product
                    .verify(vk, v, self.indicator, y, transcript)
            })
            .map_err(|_| Error::Rejected("sum check"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handle::Set;
    use ark_std::test_rng;

    // 12 rows in a domain of 16.
    const ROWS: usize = 12;

    struct Setup {
        srs: Srs,
        universe: Universe,
        v: CommittedSlice,
    }

    fn setup() -> Setup {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let universe = Universe::new(&srs, ROWS).unwrap();
        // vⱼ = j + 1.
        let v = Slice::new((1..=ROWS as u64).map(Fr::from).collect())
            .commit(&srs)
            .unwrap();
        Setup { srs, universe, v }
    }

    fn set(srs: &Srs, rows: &[usize]) -> CommittedSet {
        Set::new(rows.iter().copied()).commit(srs).unwrap()
    }

    fn prove(s: &Setup, v: &CommittedSlice, x: &CommittedSet, y: u64) -> SumCheckProof {
        let transcript = &mut Transcript::new("test");
        SumCheckProof::prove(&s.srs, &s.universe, v, x, Fr::from(y), transcript).unwrap()
    }

    fn verify(
        proof: &SumCheckProof,
        s: &Setup,
        v: &CommittedSlice,
        x: &CommittedSet,
        y: u64,
    ) -> Result<(), Error> {
        let transcript = &mut Transcript::new("test");
        proof.verify(
            &s.srs.verifier_key(),
            s.universe.handle(),
            v.handle(),
            x.handle(),
            Fr::from(y),
            transcript,
        )
    }

    #[test]
    fn accepts_sums_and_counts() {
        let s = setup();
        let ones = s.universe.ones();

        for (rows, sum) in [(vec![], 0), (vec![2, 5, 7], 17), ((0..ROWS).collect(), 78)] {
            let x = set(&s.srs, &rows);
            let proof = prove(&s, &s.v, &x, sum);
            assert_eq!(verify(&proof, &s, &s.v, &x, sum), Ok(()));

            let count = rows.len() as u64;
            let proof = prove(&s, ones, &x, count);
            assert_eq!(verify(&proof, &s, ones, &x, count), Ok(()));
        }
    }

    #[test]
    fn each_check_is_needed() {
        let s = setup();
        let x = set(&s.srs, &[2, 5, 7]);
        let honest = prove(&s, &s.v, &x, 17);
        let reject = Err(Error::Rejected("sum check"));

        // A wrong sum: only the inner product catches it.
        assert_eq!(verify(&honest, &s, &s.v, &x, 18), reject);

        // An honest proof for X ∪ {9}: only the tie of the nullifying test's complement to X̃
        // catches it.
        let other = prove(&s, &s.v, &set(&s.srs, &[2, 5, 7, 9]), 27);
        assert_eq!(verify(&other, &s, &s.v, &x, 27), reject);

        // The indicator of X ∪ {9}, with the honest nullifying proof for X: only the nullifying
        // test catches it.
        let forged = SumCheckProof {
            indicator: other.indicator,
            inner_product: other.inner_product,
            ..honest
        };
        assert_eq!(verify(&forged, &s, &s.v, &x, 27), reject);
    }
}
