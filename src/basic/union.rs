//! Union test `W̃ = S̃₁ ∪ … ∪ S̃ₖ` (Fig. 8).
//!
//! `W = ∪ Sᵢ` if and only if `Sᵢ ⊆ W` for every `i` and the leftovers `Cᵢ = W ∖ Sᵢ` have no
//! common row: a row of `W` in no `Sᵢ` would be in every `Cᵢ`. The verifier checks
//! `e(S̃ᵢ, [P_{Cᵢ}]₂) = e(W̃, [1]₂)`, i.e. `P_{Sᵢ} · P_{Cᵢ} = P_W`, for every `i`, and that the
//! `Cᵢ` have no common row, with a Bézout identity `Σ qᵢ · P_{Cᵢ} = 1`.
//!
//! Instead of the paper's `∪ Sᵢ = ¬(∩ ¬Sᵢ)`, with complements over all rows, the leftovers are
//! complements within `W`: the prover works on `|W|` rows instead of all of them.

use super::coprime::CoprimeProof;
use crate::Error;
use crate::handle::{CommittedSet, Set, SetHandle};
use crate::setup::Srs;
use crate::transcript::Transcript;
use ark_bls12_381::Fr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Proof that a set is the union of other sets.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct UnionProof(pub(crate) CoprimeProof);

impl UnionProof {
    /// Proves `W = S₁ ∪ … ∪ Sₖ`, for `k ≥ 1`.
    pub fn prove(
        srs: &Srs,
        sets: &[&CommittedSet],
        union: &CommittedSet,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let actual = Set::new(sets.iter().flat_map(|set| set.set().rows()).copied());
        if sets.is_empty() || &actual != union.set() {
            return Err(Error::InvalidWitness("union test"));
        }

        let rows = union.set().rows();
        let leftovers: Vec<Set> = sets
            .iter()
            .map(|set| {
                let set = set.set().rows();
                Set::new(
                    rows.iter()
                        .copied()
                        .filter(|row| set.binary_search(row).is_err()),
                )
            })
            .collect();
        let proof = Self(CoprimeProof::prove(srs, &leftovers, "union test")?);
        let handles: Vec<SetHandle> = sets.iter().map(|set| set.handle()).collect();
        proof.challenge(&handles, union.handle(), transcript);
        Ok(proof)
    }

    /// Verifies `W = S₁ ∪ … ∪ Sₖ` for the sets of the given handles.
    pub fn verify(
        &self,
        sets: &[SetHandle],
        union: SetHandle,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        let rho = self.challenge(sets, union, transcript);
        let pairs: Vec<_> = sets.iter().map(|set| (set.0, union.0)).collect();
        if !self.0.verify(&pairs, rho) {
            return Err(Error::Rejected("union test"));
        }
        Ok(())
    }

    fn challenge(&self, sets: &[SetHandle], union: SetHandle, transcript: &mut Transcript) -> Fr {
        transcript.append("union test: sets", sets);
        transcript.append("union test: union", &union);
        transcript.append("union test: proof", self);
        transcript.challenge("union test: rho")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::G1Projective;
    use ark_ff::Zero;
    use ark_std::test_rng;

    fn set(srs: &Srs, rows: &[usize]) -> CommittedSet {
        Set::new(rows.iter().copied()).commit(srs).unwrap()
    }

    fn prove(srs: &Srs, sets: &[&CommittedSet], union: &CommittedSet) -> Result<UnionProof, Error> {
        UnionProof::prove(srs, sets, union, &mut Transcript::new("test"))
    }

    fn verify(
        proof: &UnionProof,
        sets: &[&CommittedSet],
        union: &CommittedSet,
    ) -> Result<(), Error> {
        let handles: Vec<SetHandle> = sets.iter().map(|set| set.handle()).collect();
        proof.verify(&handles, union.handle(), &mut Transcript::new("test"))
    }

    #[test]
    fn accepts_unions() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let cases: [(&[&[usize]], &[usize]); 5] = [
            (&[&[0, 1, 9], &[1, 4, 9], &[5, 15]], &[0, 1, 4, 5, 9, 15]),
            (&[&[2, 3], &[2, 3]], &[2, 3]),
            (&[&[1, 4, 7]], &[1, 4, 7]),
            (&[&[], &[]], &[]),
            // The union is the whole domain.
            (
                &[
                    &[0, 1, 2, 3, 4, 5, 6, 7, 8],
                    &[8, 9, 10, 11, 12, 13, 14, 15],
                ],
                &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            ),
        ];

        for (rows, union) in cases {
            let sets: Vec<CommittedSet> = rows.iter().map(|rows| set(&srs, rows)).collect();
            let sets: Vec<&CommittedSet> = sets.iter().collect();
            let union = set(&srs, union);
            let proof = prove(&srs, &sets, &union).unwrap();
            assert_eq!(verify(&proof, &sets, &union), Ok(()));
        }
    }

    #[test]
    fn rejects_a_union_with_an_extra_row() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let (a, b) = (set(&srs, &[0, 2]), set(&srs, &[2, 3]));
        // Row 5 is in no set: both leftovers contain it, so no Bézout coefficients exist.
        let extra = set(&srs, &[0, 2, 3, 5]);
        let forged = UnionProof(CoprimeProof {
            sets_g2: [&[3, 5][..], &[0, 5]]
                .iter()
                .map(|rows| srs.commit_g2(set(&srs, rows).polynomial()).unwrap())
                .collect(),
            bezout_g1: vec![G1Projective::zero(); 2],
        });

        assert_eq!(
            verify(&forged, &[&a, &b], &extra),
            Err(Error::Rejected("union test"))
        );
        assert_eq!(
            prove(&srs, &[&a, &b], &extra),
            Err(Error::InvalidWitness("union test"))
        );
    }

    #[test]
    fn rejects_a_union_missing_a_row() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let (a, b) = (set(&srs, &[0, 2]), set(&srs, &[2, 3]));
        let honest = prove(&srs, &[&a, &b], &set(&srs, &[0, 2, 3])).unwrap();
        // The Bézout equation still holds: only the containment catches the missing row 3.
        let missing = set(&srs, &[0, 2]);

        assert_eq!(
            verify(&honest, &[&a, &b], &missing),
            Err(Error::Rejected("union test"))
        );
    }
}
