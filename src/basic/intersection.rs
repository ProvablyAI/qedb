//! Intersection test `Ĩ = S̃₁ ∩ … ∩ S̃ₖ` (Fig. 5, Fig. 8).
//!
//! `I = ∩ Sᵢ` if and only if `I ⊆ Sᵢ` for every `i` and the differences `Dᵢ = Sᵢ ∖ I` have no
//! common row. The verifier checks `e(Ĩ, [P_{Dᵢ}]₂) = e(S̃ᵢ, [1]₂)`, i.e. `P_I · P_{Dᵢ} = P_{Sᵢ}`,
//! for every `i`, and that the `Dᵢ` have no common row, with a Bézout identity `Σ qᵢ · P_{Dᵢ} = 1`.

use super::coprime::CoprimeProof;
use crate::Error;
use crate::handle::{CommittedSet, Set, SetHandle};
use crate::setup::Srs;
use crate::transcript::Transcript;
use ark_bls12_381::Fr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Proof that a set is the intersection of other sets.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct IntersectionProof(pub(crate) CoprimeProof);

impl IntersectionProof {
    /// Proves `I = S₁ ∩ … ∩ Sₖ`, for `k ≥ 1`.
    pub fn prove(
        srs: &Srs,
        sets: &[&CommittedSet],
        intersection: &CommittedSet,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let rows = intersection.set().rows();
        let Some((first, rest)) = sets.split_first() else {
            return Err(Error::InvalidWitness("intersection test"));
        };
        let actual = first.set().rows().iter().filter(|row| {
            rest.iter()
                .all(|set| set.set().rows().binary_search(row).is_ok())
        });
        if !actual.eq(rows) {
            return Err(Error::InvalidWitness("intersection test"));
        }

        let differences: Vec<Set> = sets
            .iter()
            .map(|set| set.set().difference(intersection.set()))
            .collect();
        let proof = Self(CoprimeProof::prove(srs, &differences, "intersection test")?);
        let handles: Vec<SetHandle> = sets.iter().map(|set| set.handle()).collect();
        proof.challenge(&handles, intersection.handle(), transcript);
        Ok(proof)
    }

    /// Verifies `I = S₁ ∩ … ∩ Sₖ` for the sets of the given handles.
    pub fn verify(
        &self,
        sets: &[SetHandle],
        intersection: SetHandle,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        let rho = self.challenge(sets, intersection, transcript);
        let pairs: Vec<_> = sets.iter().map(|set| (intersection.0, set.0)).collect();
        if !self.0.verify(&pairs, rho) {
            return Err(Error::Rejected("intersection test"));
        }
        Ok(())
    }

    fn challenge(
        &self,
        sets: &[SetHandle],
        intersection: SetHandle,
        transcript: &mut Transcript,
    ) -> Fr {
        transcript.append("intersection test: sets", sets);
        transcript.append("intersection test: intersection", &intersection);
        transcript.append("intersection test: proof", self);
        transcript.challenge("intersection test: rho")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{G1Projective, G2Projective};
    use ark_ec::PrimeGroup;
    use ark_ff::Zero;
    use ark_std::test_rng;

    fn set(srs: &Srs, rows: &[usize]) -> CommittedSet {
        Set::new(rows.iter().copied()).commit(srs).unwrap()
    }

    fn verify(
        proof: &IntersectionProof,
        sets: &[&CommittedSet],
        intersection: &CommittedSet,
    ) -> Result<(), Error> {
        let handles: Vec<SetHandle> = sets.iter().map(|set| set.handle()).collect();
        proof.verify(
            &handles,
            intersection.handle(),
            &mut Transcript::new("test"),
        )
    }

    #[test]
    fn accepts_intersections() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let cases: [(&[&[usize]], &[usize]); 5] = [
            (
                &[&[0, 1, 2, 3, 9], &[2, 3, 4, 9], &[2, 3, 5, 9, 15]],
                &[2, 3, 9],
            ),
            (&[&[0, 1], &[2, 3], &[4]], &[]),
            // A set equal to the intersection: an empty difference.
            (&[&[2, 3], &[2, 3, 4]], &[2, 3]),
            (&[&[1, 4, 7]], &[1, 4, 7]),
            // Every row of the domain in some difference.
            (
                &[&[0, 1, 2, 3, 4, 5, 6, 7], &[8, 9, 10, 11, 12, 13, 14, 15]],
                &[],
            ),
        ];

        for (rows, intersection) in cases {
            let sets: Vec<CommittedSet> = rows.iter().map(|rows| set(&srs, rows)).collect();
            let sets: Vec<&CommittedSet> = sets.iter().collect();
            let intersection = set(&srs, intersection);
            let proof =
                IntersectionProof::prove(&srs, &sets, &intersection, &mut Transcript::new("test"))
                    .unwrap();
            assert_eq!(verify(&proof, &sets, &intersection), Ok(()));
        }
    }

    #[test]
    fn rejects_an_intersection_missing_a_row() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let (a, b) = (set(&srs, &[0, 2, 3]), set(&srs, &[2, 3, 4]));
        // Row 3 is missing: both differences contain it, so no Bézout coefficients exist.
        let missing = set(&srs, &[2]);
        let forged = IntersectionProof(CoprimeProof {
            sets_g2: [&[0, 3][..], &[3, 4]]
                .iter()
                .map(|rows| srs.commit_g2(set(&srs, rows).polynomial()).unwrap())
                .collect(),
            bezout_g1: vec![G1Projective::zero(); 2],
        });

        assert_eq!(
            verify(&forged, &[&a, &b], &missing),
            Err(Error::Rejected("intersection test"))
        );
        assert_eq!(
            IntersectionProof::prove(&srs, &[&a, &b], &missing, &mut Transcript::new("test")),
            Err(Error::InvalidWitness("intersection test"))
        );
    }

    #[test]
    fn rejects_an_intersection_with_an_extra_row() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let (a, b) = (set(&srs, &[0, 2, 3]), set(&srs, &[2, 3, 4]));
        let honest = IntersectionProof::prove(
            &srs,
            &[&a, &b],
            &set(&srs, &[2, 3]),
            &mut Transcript::new("test"),
        )
        .unwrap();
        // The Bézout equation still holds: only the containment catches row 4.
        let extra = set(&srs, &[2, 3, 4]);

        assert_eq!(
            verify(&honest, &[&a, &b], &extra),
            Err(Error::Rejected("intersection test"))
        );
    }

    #[test]
    fn rejects_an_extra_bezout_pair() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let (a, b) = (set(&srs, &[0, 2, 3]), set(&srs, &[2, 3, 4]));
        let mut proof = IntersectionProof::prove(
            &srs,
            &[&a, &b],
            &set(&srs, &[2, 3]),
            &mut Transcript::new("test"),
        )
        .unwrap();
        proof.0.sets_g2.push(G2Projective::generator());
        proof.0.bezout_g1.push(G1Projective::generator());

        assert_eq!(
            verify(&proof, &[&a, &b], &set(&srs, &[2, 3])),
            Err(Error::Rejected("intersection test"))
        );
    }
}
