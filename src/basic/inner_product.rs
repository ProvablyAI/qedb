//! Inner-product test `⟨ũ, ṽ⟩ = y` (Fig. 8), with the linear-map vector commitment of Fig. 4.
//!
//! The sum over `H` of a polynomial of degree `< N` is `N` times its constant term, so
//! `⟨u, v⟩ = y` if and only if `u(x)·v(x) − y/N = x·R(x) + Z_H(x)·H(x)` for some `R` of degree
//! `≤ N − 2` and some `H`, with `Z_H = xᴺ − 1`. The prover sends `[R]₁`, `[H]₁`, `[x²R]₁` and
//! `[v]₂`; the verifier checks
//!
//! 1. `e(ũ, [v]₂) = e(y/N·[1]₁, [1]₂) + e([R]₁, [τ]₂) + e([H]₁, [Z_H]₂)`;
//! 2. `e(ṽ, [1]₂) = e([1]₁, [v]₂)`: `[v]₂` is the slice of the handle `ṽ`;
//! 3. `e([R]₁, [τ²]₂) = e([x²R]₁, [1]₂)`: `deg R ≤ N − 2`, since the SRS stops at degree `N`;
//!
//! batched with a challenge `ρ` as one multi-pairing. Without 3, the prover could move a wrong
//! `y` into the coefficient of `x^{N−1}` of `R`.

use crate::Error;
use crate::handle::{CommittedSlice, SliceHandle};
use crate::setup::{Srs, VerifierKey};
use crate::transcript::Transcript;
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::PrimeGroup;
use ark_ec::pairing::Pairing;
use ark_ff::{Field, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::*;

/// Proof of the inner product of two slices.
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct InnerProductProof {
    /// `[R(τ)]₁`.
    pub(crate) remainder: G1Projective,
    /// `[H(τ)]₁`.
    pub(crate) quotient: G1Projective,
    /// `[τ²R(τ)]₁`.
    pub(crate) shifted_remainder: G1Projective,
    /// `[v(τ)]₂`.
    pub(crate) v_g2: G2Projective,
}

impl InnerProductProof {
    /// Proves `⟨u, v⟩ = y`.
    pub fn prove(
        srs: &Srs,
        u: &CommittedSlice,
        v: &CommittedSlice,
        y: Fr,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let actual: Fr = u
            .slice()
            .values()
            .par_iter()
            .zip(v.slice().values())
            .map(|(a, b)| *a * b)
            .sum();
        if actual != y {
            return Err(Error::InvalidWitness("inner product test"));
        }

        // u·v = (y/N + x·R) + Z_H·H.
        let (quotient, remainder) =
            (u.polynomial() * v.polynomial()).divide_by_vanishing_poly(*srs.domain());
        let r = remainder.coeffs.get(1..).unwrap_or_default();
        let shifted: Vec<Fr> = [Fr::zero(), Fr::zero()].iter().chain(r).copied().collect();

        let proof = Self {
            remainder: srs.commit_g1(r)?,
            quotient: srs.commit_g1(&quotient)?,
            shifted_remainder: srs.commit_g1(&shifted)?,
            v_g2: srs.commit_g2(v.polynomial())?,
        };
        proof.challenge(u.handle(), v.handle(), y, transcript);
        Ok(proof)
    }

    /// Verifies `⟨u, v⟩ = y` for the slices of the given handles.
    pub fn verify(
        &self,
        vk: &VerifierKey,
        u: SliceHandle,
        v: SliceHandle,
        y: Fr,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        let rho = self.challenge(u, v, y, transcript);
        let rho2 = rho.square();
        let g1 = G1Projective::generator();
        let domain = vk.domain();
        let tau = G2Projective::from(vk.tau);
        let tau2 = G2Projective::from(vk.tau_squared);
        let z_h = G2Projective::from(vk.tau_n) - G2Projective::generator();

        // Equation 1 + ρ·(2) + ρ²·(3), grouped by the G2 element.
        let check = Bls12_381::multi_pairing(
            [
                u.0 - g1 * rho,
                v.0 * rho - g1 * (y * domain.size_inv) - self.shifted_remainder * rho2,
                -self.remainder,
                -self.quotient,
                self.remainder * rho2,
            ],
            [self.v_g2, G2Projective::generator(), tau, z_h, tau2],
        );
        if !check.is_zero() {
            return Err(Error::Rejected("inner product test"));
        }
        Ok(())
    }

    fn challenge(&self, u: SliceHandle, v: SliceHandle, y: Fr, transcript: &mut Transcript) -> Fr {
        transcript.append("inner product test: u", &u);
        transcript.append("inner product test: v", &v);
        transcript.append("inner product test: y", &y);
        transcript.append("inner product test: proof", self);
        transcript.challenge("inner product test: rho")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handle::Slice;
    use ark_ff::UniformRand;
    use ark_poly::EvaluationDomain;
    use ark_std::test_rng;

    fn slice(srs: &Srs, values: Vec<Fr>) -> CommittedSlice {
        Slice::new(values).commit(srs).unwrap()
    }

    fn inner_product(u: &CommittedSlice, v: &CommittedSlice) -> Fr {
        let (u, v) = (u.slice().values(), v.slice().values());
        u.iter().zip(v).map(|(a, b)| *a * b).sum()
    }

    fn prove(
        srs: &Srs,
        u: &CommittedSlice,
        v: &CommittedSlice,
        y: Fr,
    ) -> Result<InnerProductProof, Error> {
        InnerProductProof::prove(srs, u, v, y, &mut Transcript::new("test"))
    }

    fn verify(
        proof: &InnerProductProof,
        srs: &Srs,
        u: &CommittedSlice,
        v: &CommittedSlice,
        y: Fr,
    ) -> Result<(), Error> {
        let vk = &srs.verifier_key();
        proof.verify(vk, u.handle(), v.handle(), y, &mut Transcript::new("test"))
    }

    #[test]
    fn accepts_inner_products() {
        let rng = &mut test_rng();
        let srs = Srs::setup(16, rng).unwrap();
        // Shorter than the domain: zero on the last rows.
        let u = slice(&srs, (0..13).map(|_| Fr::rand(rng)).collect());
        let random = slice(&srs, (0..16).map(|_| Fr::rand(rng)).collect());
        // An indicator vector, as in the sum check.
        let indicator = slice(&srs, (0..16).map(|i| Fr::from(i % 3 == 0)).collect());

        for v in [&random, &indicator] {
            let y = inner_product(&u, v);
            let proof = prove(&srs, &u, v, y).unwrap();
            assert_eq!(verify(&proof, &srs, &u, v, y), Ok(()));
        }
    }

    #[test]
    fn rejects_a_wrong_value() {
        let rng = &mut test_rng();
        let srs = Srs::setup(16, rng).unwrap();
        let u = slice(&srs, (0..16).map(|_| Fr::rand(rng)).collect());
        let v = slice(&srs, (0..16).map(|_| Fr::rand(rng)).collect());
        let y = inner_product(&u, &v);
        let proof = prove(&srs, &u, &v, y).unwrap();

        assert_eq!(
            verify(&proof, &srs, &u, &v, y + Fr::ONE),
            Err(Error::Rejected("inner product test"))
        );
        assert_eq!(
            prove(&srs, &u, &v, y + Fr::ONE),
            Err(Error::InvalidWitness("inner product test"))
        );
    }

    #[test]
    fn rejects_a_g2_copy_of_another_slice() {
        let rng = &mut test_rng();
        let srs = Srs::setup(16, rng).unwrap();
        let u = slice(&srs, (0..16).map(|_| Fr::rand(rng)).collect());
        let v = slice(&srs, (0..16).map(|_| Fr::rand(rng)).collect());
        let other = slice(&srs, (0..16).map(|_| Fr::rand(rng)).collect());
        // An honest proof for ⟨u, other⟩: only the tie of [v]₂ to ṽ catches it.
        let y = inner_product(&u, &other);
        let proof = prove(&srs, &u, &other, y).unwrap();

        assert_eq!(
            verify(&proof, &srs, &u, &v, y),
            Err(Error::Rejected("inner product test"))
        );
    }

    #[test]
    fn rejects_a_remainder_of_degree_n_minus_1() {
        let rng = &mut test_rng();
        let srs = Srs::setup(16, rng).unwrap();
        let n = srs.domain().size();
        let u = slice(&srs, (0..16).map(|_| Fr::rand(rng)).collect());
        let v = slice(&srs, (0..16).map(|_| Fr::rand(rng)).collect());
        let y = inner_product(&u, &v);
        let wrong = y + Fr::ONE;

        // u·v − wrong/N = x·R' + Z_H·H' with R' = R + c·x^{N−1}, H' = H − c, c = (y − wrong)/N:
        // the difference c·xᴺ − c is c·Z_H.
        let c = (y - wrong) * srs.domain().size_inv;
        let (mut h, remainder) =
            (u.polynomial() * v.polynomial()).divide_by_vanishing_poly(*srs.domain());
        let mut r = remainder.coeffs[1..].to_vec();
        r.resize(n, Fr::zero());
        r[n - 1] += c;
        h.coeffs[0] -= c;
        let forged = InnerProductProof {
            remainder: srs.commit_g1(&r).unwrap(),
            quotient: srs.commit_g1(&h).unwrap(),
            // x²R' has degree N + 1: the prover cannot commit to it.
            shifted_remainder: G1Projective::zero(),
            v_g2: srs.commit_g2(v.polynomial()).unwrap(),
        };

        assert_eq!(
            verify(&forged, &srs, &u, &v, wrong),
            Err(Error::Rejected("inner product test"))
        );
    }
}
