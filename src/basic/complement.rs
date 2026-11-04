//! Complement test `Ỹ = Ũ ∖ X̃` (Fig. 8), with `U` the rows of the table.
//!
//! `P_U` is square-free, so `Y = U ∖ X` if and only if `P_X · P_Y = P_U`. The prover sends
//! `[P_Y(τ)]₂` and the verifier checks
//!
//! 1. `e(X̃, [P_Y]₂) = e(Ũ, [1]₂)`: `P_X · P_Y = P_U`;
//! 2. `e([1]₁, [P_Y]₂) = e(Ỹ, [1]₂)`: `[P_Y]₂` is the set of the handle `Ỹ`;
//!
//! batched with a challenge `ρ` as `e(X̃ + ρ[1]₁, [P_Y]₂) = e(Ũ + ρỸ, [1]₂)`.

use crate::Error;
use crate::handle::{CommittedSet, Set, SetHandle};
use crate::setup::Srs;
use crate::transcript::Transcript;
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::PrimeGroup;
use ark_ec::pairing::Pairing;
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Proof that a set is the complement of another.
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ComplementProof {
    /// `[P_Y(τ)]₂`: once the proof verifies, the handle of `Y` in G2.
    pub(crate) complement_g2: G2Projective,
}

impl ComplementProof {
    /// Proves `Y = U ∖ X`.
    pub fn prove(
        srs: &Srs,
        universe: &CommittedSet,
        x: &CommittedSet,
        y: &CommittedSet,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let (x_rows, y_rows) = (x.set().rows(), y.set().rows());
        let union = Set::new(x_rows.iter().chain(y_rows).copied());
        if x_rows.len() + y_rows.len() != union.rows().len() || &union != universe.set() {
            return Err(Error::InvalidWitness("complement test"));
        }

        let proof = Self {
            complement_g2: srs.commit_g2(y.polynomial())?,
        };
        proof.challenge(universe.handle(), x.handle(), y.handle(), transcript);
        Ok(proof)
    }

    /// Verifies `Y = U ∖ X` for the sets of the given handles.
    pub fn verify(
        &self,
        universe: SetHandle,
        x: SetHandle,
        y: SetHandle,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        let rho = self.challenge(universe, x, y, transcript);
        let check = Bls12_381::multi_pairing(
            [
                x.0 + G1Projective::generator() * rho,
                -(universe.0 + y.0 * rho),
            ],
            [self.complement_g2, G2Projective::generator()],
        );
        if !check.is_zero() {
            return Err(Error::Rejected("complement test"));
        }
        Ok(())
    }

    fn challenge(
        &self,
        universe: SetHandle,
        x: SetHandle,
        y: SetHandle,
        transcript: &mut Transcript,
    ) -> Fr {
        transcript.append("complement test: universe", &universe);
        transcript.append("complement test: set", &x);
        transcript.append("complement test: complement", &y);
        transcript.append("complement test: proof", self);
        transcript.challenge("complement test: rho")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::test_rng;

    // 6 rows in a domain of 8: rows 6 and 7 are padding.
    const ROWS: usize = 6;

    fn set(srs: &Srs, rows: impl IntoIterator<Item = usize>) -> CommittedSet {
        Set::new(rows).commit(srs).unwrap()
    }

    fn verify(
        proof: &ComplementProof,
        universe: &CommittedSet,
        x: &CommittedSet,
        y: &CommittedSet,
    ) -> Result<(), Error> {
        proof.verify(
            universe.handle(),
            x.handle(),
            y.handle(),
            &mut Transcript::new("test"),
        )
    }

    #[test]
    fn accepts_complements() {
        let srs = Srs::setup(8, &mut test_rng()).unwrap();
        let universe = set(&srs, 0..ROWS);

        for rows in [vec![], vec![1, 4], (0..ROWS).collect()] {
            let x = set(&srs, rows.clone());
            let y = set(&srs, (0..ROWS).filter(|row| !rows.contains(row)));
            let proof =
                ComplementProof::prove(&srs, &universe, &x, &y, &mut Transcript::new("test"))
                    .unwrap();
            assert_eq!(verify(&proof, &universe, &x, &y), Ok(()));
        }
    }

    #[test]
    fn rejects_a_complement_handle_not_tied_to_the_proof() {
        let srs = Srs::setup(8, &mut test_rng()).unwrap();
        let universe = set(&srs, 0..ROWS);
        let x = set(&srs, [1, 4]);
        let y = set(&srs, [0, 2, 3, 5]);
        let proof =
            ComplementProof::prove(&srs, &universe, &x, &y, &mut Transcript::new("test")).unwrap();
        // Equation 1 still holds: only the tie catches the other handle.
        let other = set(&srs, [0, 2, 3]);

        assert_eq!(
            verify(&proof, &universe, &x, &other),
            Err(Error::Rejected("complement test"))
        );
    }

    #[test]
    fn rejects_a_complement_with_a_padding_row() {
        let srs = Srs::setup(8, &mut test_rng()).unwrap();
        let universe = set(&srs, 0..ROWS);
        let x = set(&srs, [1, 4]);
        let y = set(&srs, [0, 2, 3, 5, 7]);
        let forged = ComplementProof {
            complement_g2: srs.commit_g2(y.polynomial()).unwrap(),
        };

        assert_eq!(
            verify(&forged, &universe, &x, &y),
            Err(Error::Rejected("complement test"))
        );
        assert_eq!(
            ComplementProof::prove(&srs, &universe, &x, &y, &mut Transcript::new("test")),
            Err(Error::InvalidWitness("complement test"))
        );
    }
}
