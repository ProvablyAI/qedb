//! Structured reference string (SRS) and evaluation domain.

use crate::Error;
use ark_bls12_381::{Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup, ScalarMul, VariableBaseMSM};
use ark_ff::{Field, UniformRand, Zero, batch_inversion};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;
use rayon::prelude::*;
use std::iter;

/// Evaluation domain `H = {ω⁰, …, ω^(N−1)}`: row `i` is `ωⁱ`.
pub type Domain = Radix2EvaluationDomain<Fr>;

/// Powers `[τⁱ]₁` and `[τⁱ]₂` for `i = 0, …, N`, with `N` the domain size, and the Lagrange basis
/// `[λᵢ(τ)]₁` for `i < N`.
///
/// Degree `N` is needed for the vanishing polynomial of a set of `N` rows. Slices are committed in
/// the Lagrange basis, from their values: an MSM over the non-zero values only, faster for small
/// values (bits, 64-bit integers) than one over the coefficients.
#[derive(Clone, Debug)]
pub struct Srs {
    g1: Vec<G1Affine>,
    g2: Vec<G2Affine>,
    lagrange: Vec<G1Affine>,
    domain: Domain,
}

impl Srs {
    /// Samples `τ` and builds the SRS for at least `n` rows (`N` is `n` rounded up to a power of
    /// two, and at least 2).
    pub fn setup<R: Rng + ?Sized>(n: usize, rng: &mut R) -> Result<Self, Error> {
        let domain = Domain::new(n.max(2)).ok_or(Error::Domain(n))?;
        // τ ∉ H, so that λᵢ(τ) below is well defined; any other τ is drawn with negligible
        // probability.
        let tau = loop {
            let tau = Fr::rand(rng);
            if !domain.evaluate_vanishing_polynomial(tau).is_zero() {
                break tau;
            }
        };
        let powers: Vec<Fr> = iter::successors(Some(Fr::ONE), |p| Some(*p * tau))
            .take(domain.size() + 1)
            .collect();
        let g1 = G1Projective::generator();

        Ok(Self {
            g1: g1.batch_mul(&powers),
            g2: G2Projective::generator().batch_mul(&powers),
            lagrange: g1.batch_mul(&lagrange_at(&domain, tau)),
            domain,
        })
    }

    /// The SRS of the powers `[τⁱ]₁` and `[τⁱ]₂`, `i = 0, …, N`, and the Lagrange basis
    /// `[λᵢ(τ)]₁`, `i < N`, for example from storage or from a ceremony. `N` must be a power of
    /// two, at least 2. The points are not checked: they must come from a trusted source.
    pub fn new(
        g1: Vec<G1Affine>,
        g2: Vec<G2Affine>,
        lagrange: Vec<G1Affine>,
    ) -> Result<Self, Error> {
        let domain = domain_of(&g1, &g2)?;
        if lagrange.len() != domain.size() {
            return Err(Error::Domain(lagrange.len()));
        }

        Ok(Self {
            g1,
            g2,
            lagrange,
            domain,
        })
    }

    /// The SRS of the powers `[τⁱ]₁` and `[τⁱ]₂`, `i = 0, …, N`, which must start from the
    /// generators the verifier uses. A prefix of an SRS is the SRS of a smaller domain.
    ///
    /// Computes the Lagrange basis from the powers, with `O(N log N)` scalar multiplications.
    pub fn from_powers(g1: Vec<G1Affine>, g2: Vec<G2Affine>) -> Result<Self, Error> {
        let domain = domain_of(&g1, &g2)?;
        if g1[0] != G1Affine::generator() || g2[0] != G2Affine::generator() {
            return Err(Error::Generators);
        }
        // [λᵢ(τ)]₁ = Σⱼ (ω^(−ij)/N)·[τʲ]₁: the inverse FFT of the powers.
        let powers: Vec<G1Projective> = g1[..domain.size()].par_iter().map(|&p| p.into()).collect();
        let lagrange = G1Projective::normalize_batch(&domain.ifft(&powers));

        Ok(Self {
            g1,
            g2,
            lagrange,
            domain,
        })
    }

    /// The powers `[τⁱ]₁`, `i = 0, …, N`.
    pub fn g1(&self) -> &[G1Affine] {
        &self.g1
    }

    /// The powers `[τⁱ]₂`, `i = 0, …, N`.
    pub fn g2(&self) -> &[G2Affine] {
        &self.g2
    }

    /// The Lagrange basis `[λᵢ(τ)]₁`, `i < N`.
    pub fn lagrange(&self) -> &[G1Affine] {
        &self.lagrange
    }

    /// The evaluation domain `H`.
    pub const fn domain(&self) -> &Domain {
        &self.domain
    }

    /// `[v(τ)]₁` for the polynomial `v` with values `v(ωⁱ) = vᵢ`, `0` after the last value.
    pub fn commit_lagrange(&self, values: &[Fr]) -> Result<G1Projective, Error> {
        if values.len() > self.domain.size() {
            return Err(Error::RowOutOfDomain {
                row: values.len() - 1,
                size: self.domain.size(),
            });
        }
        commit(&self.lagrange, values)
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

/// The domain of the powers `g1` and `g2`, `N + 1` of each.
fn domain_of(g1: &[G1Affine], g2: &[G2Affine]) -> Result<Domain, Error> {
    let n = g1.len().saturating_sub(1);
    Domain::new(n)
        .filter(|domain| domain.size() == n && n >= 2 && g2.len() == g1.len())
        .ok_or(Error::Domain(n))
}

/// `λᵢ(τ) = ωⁱ·(τᴺ − 1) / (N·(τ − ωⁱ))` for `i < N`, with `τ ∉ H`.
fn lagrange_at(domain: &Domain, tau: Fr) -> Vec<Fr> {
    let points: Vec<Fr> = domain.elements().collect();
    let mut denominators: Vec<Fr> = points.par_iter().map(|w| tau - w).collect();
    batch_inversion(&mut denominators);
    let scale = domain.evaluate_vanishing_polynomial(tau) * domain.size_inv;
    points
        .par_iter()
        .zip(&denominators)
        .map(|(w, d)| *w * d * scale)
        .collect()
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
    fn the_lagrange_basis_of_tau_is_the_one_of_the_powers() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let from_powers = Srs::from_powers(srs.g1().to_vec(), srs.g2().to_vec()).unwrap();

        assert_eq!(from_powers.lagrange(), srs.lagrange());
    }

    #[test]
    fn commits_values_as_their_polynomial() {
        let rng = &mut test_rng();
        let srs = Srs::setup(16, rng).unwrap();
        let domain = srs.domain();

        // Shorter than the domain: zero on the last rows.
        for len in [0, 5, 16] {
            let values: Vec<Fr> = (0..len).map(|_| Fr::rand(rng)).collect();
            let mut padded = values.clone();
            padded.resize(domain.size(), Fr::zero());
            assert_eq!(
                srs.commit_lagrange(&values),
                srs.commit_g1(&domain.ifft(&padded))
            );
        }
        assert_eq!(
            srs.commit_lagrange(&[Fr::ONE; 17]),
            Err(Error::RowOutOfDomain { row: 16, size: 16 })
        );
    }

    #[test]
    fn takes_a_stored_lagrange_basis() {
        let srs = Srs::setup(8, &mut test_rng()).unwrap();
        let new = |basis: &[G1Affine]| {
            Srs::new(srs.g1().to_vec(), srs.g2().to_vec(), basis.to_vec()).map(|srs| srs.lagrange)
        };

        assert_eq!(new(srs.lagrange()), Ok(srs.lagrange.clone()));
        assert_eq!(new(&srs.lagrange()[..4]), Err(Error::Domain(4)));
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
