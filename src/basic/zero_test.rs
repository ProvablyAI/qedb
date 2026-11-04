//! Zero test `v[S] = 0` (Fig. 8, App. D.3): the slice `v` is zero on every row of the set `S`.
//!
//! `v` vanishes on `S` if and only if `P_S` divides `v(x)`. The prover sends `[q(τ)]₁` with
//! `q = v / P_S`, and `[P_S(τ)]₂`. The verifier checks
//!
//! 1. `e([q]₁, [P_S]₂) = e([v]₁, [1]₂)`: `q · P_S = v`;
//! 2. `e([1]₁, [P_S]₂) = e(S̃, [1]₂)`: `[P_S]₂` is the set of the handle `S̃`;
//!
//! batched with a challenge `ρ` as `e([q]₁ + ρ[1]₁, [P_S]₂) = e([v]₁ + ρS̃, [1]₂)`.

use crate::Error;
use crate::handle::{CommittedSet, CommittedSlice, SetHandle, SliceHandle};
use crate::setup::{Domain, Srs};
use crate::transcript::Transcript;
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::PrimeGroup;
use ark_ec::pairing::Pairing;
use ark_ff::{FftField, Zero, batch_inversion};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::*;

/// Proof that a slice is zero on a set.
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ZeroTestProof {
    /// `[q(τ)]₁` with `q = v / P_S`.
    pub(crate) quotient: G1Projective,
    /// `[P_S(τ)]₂`: once the proof verifies, the handle of `S` in G2.
    pub(crate) set_g2: G2Projective,
}

impl ZeroTestProof {
    /// Proves `v[S] = 0`.
    pub fn prove(
        srs: &Srs,
        v: &CommittedSlice,
        s: &CommittedSet,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let values = v.slice().values();
        if let Some(&row) = s
            .set()
            .rows()
            .iter()
            .find(|&&row| values.get(row).is_some_and(|value| !value.is_zero()))
        {
            return Err(Error::NotZero { row });
        }

        let q = divide_exact(v.polynomial(), s.polynomial())?;
        let proof = Self {
            quotient: srs.commit_g1(&q)?,
            set_g2: srs.commit_g2(s.polynomial())?,
        };
        proof.challenge(v.handle(), s.handle(), transcript);
        Ok(proof)
    }

    /// Verifies `v[S] = 0` for the slice and set of the given handles.
    pub fn verify(
        &self,
        v: SliceHandle,
        s: SetHandle,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        let rho = self.challenge(v, s, transcript);
        let check = Bls12_381::multi_pairing(
            [
                self.quotient + G1Projective::generator() * rho,
                -(v.0 + s.0 * rho),
            ],
            [self.set_g2, G2Projective::generator()],
        );
        if !check.is_zero() {
            return Err(Error::Rejected("zero test"));
        }
        Ok(())
    }

    fn challenge(&self, v: SliceHandle, s: SetHandle, transcript: &mut Transcript) -> Fr {
        transcript.append("zero test: slice", &v);
        transcript.append("zero test: set", &s);
        transcript.append("zero test: proof", self);
        transcript.challenge("zero test: rho")
    }
}

/// `v / p` for `p` dividing `v`: two FFTs on a coset, a point-wise division and an inverse FFT.
///
/// `p` does not vanish on the coset: its roots are in `H`, and the coset `g·H'`, with `g` the
/// generator of the multiplicative group, contains no element of a subgroup of order `2ᵏ`.
fn divide_exact(
    v: &DensePolynomial<Fr>,
    p: &DensePolynomial<Fr>,
) -> Result<DensePolynomial<Fr>, Error> {
    let size = v.coeffs.len().max(p.coeffs.len());
    let coset = Domain::new(size)
        .and_then(|domain| domain.get_coset(Fr::GENERATOR))
        .ok_or(Error::Domain(size))?;

    let mut p_evals = coset.fft(&p.coeffs);
    batch_inversion(&mut p_evals);
    let mut evals = coset.fft(&v.coeffs);
    evals
        .par_iter_mut()
        .zip(&p_evals)
        .for_each(|(v, p_inv)| *v *= p_inv);
    Ok(DensePolynomial::from_coefficients_vec(coset.ifft(&evals)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handle::{Set, Slice};
    use ark_std::test_rng;

    fn slice(srs: &Srs, values: &[u64]) -> CommittedSlice {
        Slice::new(values.iter().map(|&x| Fr::from(x)).collect())
            .commit(srs)
            .unwrap()
    }

    fn set(srs: &Srs, rows: impl IntoIterator<Item = usize>) -> CommittedSet {
        Set::new(rows).commit(srs).unwrap()
    }

    fn prove(srs: &Srs, v: &CommittedSlice, s: &CommittedSet) -> Result<ZeroTestProof, Error> {
        ZeroTestProof::prove(srs, v, s, &mut Transcript::new("test"))
    }

    fn verify(proof: &ZeroTestProof, v: &CommittedSlice, s: &CommittedSet) -> Result<(), Error> {
        proof.verify(v.handle(), s.handle(), &mut Transcript::new("test"))
    }

    #[test]
    fn accepts_slices_zero_on_the_set() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let v = slice(&srs, &[5, 0, 7, 0, 9, 2]);

        // Rows 6.. are after the last value, so zero.
        for rows in [vec![], vec![1, 3], vec![1, 3, 6, 15]] {
            let s = set(&srs, rows);
            let proof = prove(&srs, &v, &s).unwrap();
            assert_eq!(verify(&proof, &v, &s), Ok(()));
        }
    }

    #[test]
    fn rejects_a_proof_for_another_set() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let v = slice(&srs, &[5, 0, 7, 0, 9, 2]);
        let proof = prove(&srs, &v, &set(&srs, [1, 3])).unwrap();
        // v is zero on row 6 too: only the tie between [P_S]₂ and S̃ catches the other set.
        let other = set(&srs, [1, 3, 6]);

        assert_eq!(
            verify(&proof, &v, &other),
            Err(Error::Rejected("zero test"))
        );
    }

    #[test]
    fn rejects_the_unbatched_product_forgery() {
        // Satisfies e(q, P₂)·e([1]₁, P₂)·e(−v − S̃, [1]₂) = 1 for any v and S (C1).
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let v = slice(&srs, &[5, 1, 7]);
        let s = set(&srs, [0, 1]);
        let forged = ZeroTestProof {
            quotient: v.handle().0 + s.handle().0 - G1Projective::generator(),
            set_g2: G2Projective::generator(),
        };

        assert_eq!(verify(&forged, &v, &s), Err(Error::Rejected("zero test")));
    }

    #[test]
    fn prover_refuses_a_slice_not_zero_on_the_set() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();

        assert_eq!(
            prove(&srs, &slice(&srs, &[5, 0, 7]), &set(&srs, [1, 2])),
            Err(Error::NotZero { row: 2 })
        );
    }
}
