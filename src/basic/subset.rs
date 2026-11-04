//! Subset test `T̃ ⊆ S̃` (Fig. 8).
//!
//! `T ⊆ S` if and only if `P_T` divides `P_S`. The prover sends `[P_{S∖T}(τ)]₂` and the verifier
//! checks `e(T̃, [P_{S∖T}]₂) = e(S̃, [1]₂)`, i.e. `P_T · P_{S∖T} = P_S`.

use crate::Error;
use crate::handle::{CommittedSet, Set, SetHandle};
use crate::setup::Srs;
use crate::transcript::Transcript;
use ark_bls12_381::{Bls12_381, G2Projective};
use ark_ec::PrimeGroup;
use ark_ec::pairing::Pairing;
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Proof that a set is a subset of another.
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct SubsetProof {
    /// `[P_{S∖T}(τ)]₂`.
    pub(crate) difference_g2: G2Projective,
}

impl SubsetProof {
    /// Proves `T ⊆ S`.
    pub fn prove(
        srs: &Srs,
        t: &CommittedSet,
        s: &CommittedSet,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let (t_rows, s_rows) = (t.set().rows(), s.set().rows());
        if !t_rows.iter().all(|row| s_rows.binary_search(row).is_ok()) {
            return Err(Error::InvalidWitness("subset test"));
        }

        let difference = Set::new(
            s_rows
                .iter()
                .copied()
                .filter(|row| t_rows.binary_search(row).is_err()),
        );
        let proof = Self {
            difference_g2: srs.commit_g2(&difference.characteristic(srs.domain())?)?,
        };
        proof.append(t.handle(), s.handle(), transcript);
        Ok(proof)
    }

    /// Verifies `T ⊆ S` for the sets of the given handles.
    pub fn verify(
        &self,
        t: SetHandle,
        s: SetHandle,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        self.append(t, s, transcript);
        let check =
            Bls12_381::multi_pairing([t.0, -s.0], [self.difference_g2, G2Projective::generator()]);
        if !check.is_zero() {
            return Err(Error::Rejected("subset test"));
        }
        Ok(())
    }

    fn append(&self, t: SetHandle, s: SetHandle, transcript: &mut Transcript) {
        transcript.append("subset test: subset", &t);
        transcript.append("subset test: set", &s);
        transcript.append("subset test: proof", self);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::test_rng;

    fn set(srs: &Srs, rows: impl IntoIterator<Item = usize>) -> CommittedSet {
        Set::new(rows).commit(srs).unwrap()
    }

    #[test]
    fn accepts_subsets() {
        let srs = Srs::setup(8, &mut test_rng()).unwrap();
        let s = set(&srs, [0, 2, 5, 7]);

        for rows in [vec![], vec![2, 5], vec![0, 2, 5, 7]] {
            let t = set(&srs, rows);
            let proof = SubsetProof::prove(&srs, &t, &s, &mut Transcript::new("test")).unwrap();
            assert_eq!(
                proof.verify(t.handle(), s.handle(), &mut Transcript::new("test")),
                Ok(())
            );
        }
    }

    #[test]
    fn rejects_a_set_that_is_not_a_subset() {
        let srs = Srs::setup(8, &mut test_rng()).unwrap();
        let s = set(&srs, [0, 2, 5, 7]);
        let t = set(&srs, [2, 5]);
        let proof = SubsetProof::prove(&srs, &t, &s, &mut Transcript::new("test")).unwrap();
        let not_subset = set(&srs, [2, 6]);

        assert_eq!(
            proof.verify(
                not_subset.handle(),
                s.handle(),
                &mut Transcript::new("test")
            ),
            Err(Error::Rejected("subset test"))
        );
        assert_eq!(
            SubsetProof::prove(&srs, &not_subset, &s, &mut Transcript::new("test")),
            Err(Error::InvalidWitness("subset test"))
        );
    }
}
