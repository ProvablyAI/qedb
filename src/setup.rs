//! Structured reference string (SRS) and evaluation domain.

use crate::Error;
use ark_bls12_381::{Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, PrimeGroup, ScalarMul, VariableBaseMSM};
use ark_ff::{Field, UniformRand};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;
use std::iter;

/// Evaluation domain `H = {ω⁰, …, ω^(N−1)}`: row `i` is `ωⁱ`.
pub type Domain = Radix2EvaluationDomain<Fr>;

/// Powers `[τⁱ]₁` and `[τⁱ]₂` for `i = 0, …, N`, with `N` the domain size.
///
/// Degree `N` is needed for the vanishing polynomial of a set of `N` rows.
#[derive(Clone, Debug)]
pub struct Srs {
    g1: Vec<G1Affine>,
    g2: Vec<G2Affine>,
    domain: Domain,
}

impl Srs {
    /// Samples `τ` and builds the SRS for at least `n` rows (`N` is `n` rounded up to a power of
    /// two, and at least 2).
    pub fn setup<R: Rng + ?Sized>(n: usize, rng: &mut R) -> Result<Self, Error> {
        let domain = Domain::new(n.max(2)).ok_or(Error::Domain(n))?;
        let tau = Fr::rand(rng);
        let powers: Vec<Fr> = iter::successors(Some(Fr::ONE), |p| Some(*p * tau))
            .take(domain.size() + 1)
            .collect();

        Ok(Self {
            g1: G1Projective::generator().batch_mul(&powers),
            g2: G2Projective::generator().batch_mul(&powers),
            domain,
        })
    }

    /// The SRS of the powers `[τⁱ]₁` and `[τⁱ]₂`, `i = 0, …, N`, for example from a ceremony or
    /// from storage. `N` must be a power of two, at least 2, and the powers must start from the
    /// generators the verifier uses. The other powers are not checked: they must come from a
    /// trusted source. A prefix of an SRS is the SRS of a smaller domain.
    pub fn from_powers(g1: Vec<G1Affine>, g2: Vec<G2Affine>) -> Result<Self, Error> {
        let n = g1.len().saturating_sub(1);
        let domain = Domain::new(n)
            .filter(|domain| domain.size() == n && n >= 2 && g2.len() == g1.len())
            .ok_or(Error::Domain(n))?;
        if g1[0] != G1Affine::generator() || g2[0] != G2Affine::generator() {
            return Err(Error::Generators);
        }

        Ok(Self { g1, g2, domain })
    }

    /// The powers `[τⁱ]₁`, `i = 0, …, N`.
    pub fn g1(&self) -> &[G1Affine] {
        &self.g1
    }

    /// The powers `[τⁱ]₂`, `i = 0, …, N`.
    pub fn g2(&self) -> &[G2Affine] {
        &self.g2
    }

    /// The evaluation domain `H`.
    pub const fn domain(&self) -> &Domain {
        &self.domain
    }

    /// `[p(τ)]₁` for `p` given by its coefficients.
    pub fn commit_g1(&self, coeffs: &[Fr]) -> Result<G1Projective, Error> {
        commit(&self.g1, coeffs)
    }

    /// `[p(τ)]₂` for `p` given by its coefficients.
    pub fn commit_g2(&self, coeffs: &[Fr]) -> Result<G2Projective, Error> {
        commit(&self.g2, coeffs)
    }

    /// The part of the SRS the verifier needs.
    pub fn verifier_key(&self) -> VerifierKey {
        VerifierKey {
            domain: self.domain,
            tau: self.g2[1],
            tau_squared: self.g2[2],
            tau_n: self.g2[self.domain.size()],
            tau_n_g1: self.g1[self.domain.size()],
        }
    }
}

/// What the verifier needs from the SRS: the domain, `[τ]₂`, `[τ²]₂`, `[τᴺ]₂` and `[τᴺ]₁`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey {
    domain: Domain,
    /// `[τ]₂`.
    pub(crate) tau: G2Affine,
    /// `[τ²]₂`.
    pub(crate) tau_squared: G2Affine,
    /// `[τᴺ]₂`.
    pub(crate) tau_n: G2Affine,
    /// `[τᴺ]₁`.
    pub(crate) tau_n_g1: G1Affine,
}

impl VerifierKey {
    /// The evaluation domain `H`.
    pub const fn domain(&self) -> &Domain {
        &self.domain
    }
}

fn commit<G: VariableBaseMSM>(bases: &[G::MulBase], coeffs: &[G::ScalarField]) -> Result<G, Error> {
    let bases = bases
        .get(..coeffs.len())
        .ok_or(Error::TooManyCoefficients {
            len: coeffs.len(),
            max: bases.len(),
        })?;
    Ok(G::msm_unchecked(bases, coeffs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_poly::DenseUVPolynomial;
    use ark_poly::univariate::DensePolynomial;
    use ark_std::test_rng;

    #[test]
    fn domain_is_rounded_up() {
        let srs = Srs::setup(5, &mut test_rng()).unwrap();
        assert_eq!(srs.domain().size(), 8);
    }

    #[test]
    fn g1_and_g2_use_the_same_tau() {
        let rng = &mut test_rng();
        let srs = Srs::setup(8, rng).unwrap();
        // Degree N = 8: the largest polynomial the SRS supports.
        let p = DensePolynomial::<Fr>::rand(8, rng);

        let lhs = Bls12_381::pairing(srs.commit_g1(&p).unwrap(), G2Projective::generator());
        let rhs = Bls12_381::pairing(G1Projective::generator(), srs.commit_g2(&p).unwrap());
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn a_prefix_of_the_powers_is_a_smaller_srs() {
        let srs = Srs::setup(8, &mut test_rng()).unwrap();
        let small = Srs::from_powers(srs.g1()[..=4].to_vec(), srs.g2()[..=4].to_vec()).unwrap();

        assert_eq!(small.domain().size(), 4);
        assert_eq!(small.verifier_key().tau, srs.verifier_key().tau);
        assert_eq!(small.verifier_key().tau_n, srs.g2()[4]);
    }

    #[test]
    fn rejects_powers_without_a_domain() {
        let srs = Srs::setup(8, &mut test_rng()).unwrap();
        let powers = |n: usize| (srs.g1()[..n].to_vec(), srs.g2()[..n].to_vec());

        for n in [0, 1, 2, 4] {
            let (g1, g2) = powers(n);
            assert_eq!(
                Srs::from_powers(g1, g2).unwrap_err(),
                Error::Domain(n.saturating_sub(1))
            );
        }
        let (g1, _) = powers(5);
        let (_, g2) = powers(3);
        assert_eq!(Srs::from_powers(g1, g2).unwrap_err(), Error::Domain(4));
    }

    #[test]
    fn rejects_powers_without_the_generators() {
        let srs = Srs::setup(4, &mut test_rng()).unwrap();
        let (g1, g2) = (srs.g1().to_vec(), srs.g2().to_vec());

        let shifted = |powers: &[G1Affine]| [&powers[1..], &powers[..1]].concat();
        assert_eq!(
            Srs::from_powers(shifted(&g1), g2.clone()).unwrap_err(),
            Error::Generators
        );
        let mut other = g2;
        other.swap(0, 1);
        assert_eq!(Srs::from_powers(g1, other).unwrap_err(), Error::Generators);
    }

    #[test]
    fn rejects_polynomials_above_degree_n() {
        let rng = &mut test_rng();
        let srs = Srs::setup(8, rng).unwrap();
        let p = DensePolynomial::<Fr>::rand(9, rng);

        assert_eq!(
            srs.commit_g1(&p),
            Err(Error::TooManyCoefficients { len: 10, max: 9 })
        );
    }
}
