//! Structured reference string (SRS) and evaluation domain.

use crate::Error;
use ark_bls12_381::{Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{PrimeGroup, ScalarMul, VariableBaseMSM};
use ark_ff::{Field, UniformRand};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
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
    /// Samples `τ` and builds the SRS for at least `n` rows (`N` is `n` rounded up to a power of two).
    pub fn setup<R: Rng + ?Sized>(n: usize, rng: &mut R) -> Result<Self, Error> {
        let domain = Domain::new(n).ok_or(Error::Domain(n))?;
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
