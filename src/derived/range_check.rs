//! Range check `ṽ ∈ [0, 2^ℓ)` (Table 2): every value of `v` on the domain `H`, padding rows
//! included, is an integer in `[0, 2^ℓ)`, for `ℓ < 255` so that `2^ℓ` is below the field order.
//!
//! Instead of the paper's bit slices and nullifying tests, the bits are checked with one
//! polynomial identity. The prover commits to the bit polynomials `bᵢ`, with `v = Σᵢ 2ⁱ bᵢ`, and
//! to `q = Σᵢ ρⁱ bᵢ(bᵢ − 1) / Z_H`, a polynomial if and only if every `bᵢ` is `0` or `1` on `H`.
//! The verifier checks
//!
//! 1. `Σᵢ 2ⁱ [bᵢ] = ṽ`;
//! 2. `Σᵢ ρⁱ yᵢ(yᵢ − 1) = Z_H(γ) · y_q`, with `yᵢ = bᵢ(γ)` and `y_q = q(γ)` the claimed values;
//! 3. one opening at `γ` of `Σᵢ ηⁱ [bᵢ] + η^ℓ [q]` against `Σᵢ ηⁱ yᵢ + η^ℓ y_q`.
//!
//! `ρ` is drawn after `ṽ` and the `[bᵢ]`, `γ` after `[q]`, and `η` after the claimed values: with
//! an `η` drawn before them, the prover could pick values that satisfy 2 and agree with the
//! opening, without the `bᵢ` being bits.

use crate::Error;
use crate::basic::divide_by_linear;
use crate::handle::{CommittedSlice, SliceHandle};
use crate::setup::{Domain, Srs, VerifierKey};
use crate::transcript::Transcript;
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::pairing::Pairing;
use ark_ec::{AdditiveGroup, CurveGroup, PrimeGroup, VariableBaseMSM};
use ark_ff::{BigInteger, FftField, Field, PrimeField, Zero, batch_inversion};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain, Polynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::*;

/// The largest `ℓ`: `2^ℓ` must be below the field order.
pub const MAX_BITS: usize = Fr::MODULUS_BIT_SIZE as usize - 1;

/// Proof that every value of a slice is in `[0, 2^ℓ)`.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct RangeCheckProof {
    /// `[bᵢ(τ)]₁`.
    pub(crate) bits: Vec<G1Projective>,
    /// `[q(τ)]₁`.
    pub(crate) quotient: G1Projective,
    /// `yᵢ = bᵢ(γ)`.
    pub(crate) bit_values: Vec<Fr>,
    /// `y_q = q(γ)`.
    pub(crate) quotient_value: Fr,
    /// The opening at `γ`.
    pub(crate) opening: G1Projective,
}

impl RangeCheckProof {
    /// Proves that every value of `v` is in `[0, 2^ℓ)`, with `ℓ = ell ≤ MAX_BITS`.
    pub fn prove(
        srs: &Srs,
        v: &CommittedSlice,
        ell: usize,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let integers: Vec<_> = v
            .slice()
            .values()
            .par_iter()
            .map(|value| value.into_bigint())
            .collect();
        // The bits above the largest value are zero polynomials.
        let top = integers
            .iter()
            .map(|x| x.num_bits() as usize)
            .max()
            .unwrap_or(0);
        if ell > MAX_BITS || top > ell {
            return Err(Error::InvalidWitness("range check"));
        }

        // Sequential over the bits: the FFTs and MSMs are parallel inside.
        let domain = srs.domain();
        let bits: Vec<DensePolynomial<Fr>> = (0..ell)
            .map(|i| {
                if i >= top {
                    return DensePolynomial::zero();
                }
                let bit: Vec<Fr> = integers.iter().map(|x| Fr::from(x.get_bit(i))).collect();
                DensePolynomial::from_coefficients_vec(domain.ifft(&bit))
            })
            .collect();
        Self::prove_bits(srs, v.handle(), &bits, transcript)
    }

    /// The proof for the slice `ṽ` with the bit polynomials `bits`.
    fn prove_bits(
        srs: &Srs,
        v: SliceHandle,
        bits: &[DensePolynomial<Fr>],
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let bit_commitments = bits
            .iter()
            .map(|bit| srs.commit_g1(bit))
            .collect::<Result<Vec<_>, _>>()?;

        let rho = challenge_rho(transcript, v, bits.len(), &bit_commitments);
        let quotient = bit_quotient(srs.domain(), bits, rho)?;
        let quotient_commitment = srs.commit_g1(&quotient)?;
        let gamma = challenge_gamma(transcript, quotient_commitment);
        let bit_values: Vec<Fr> = bits.iter().map(|bit| bit.evaluate(&gamma)).collect();
        let quotient_value = quotient.evaluate(&gamma);
        let eta = challenge_eta(transcript, &bit_values, quotient_value);
        let opening = opening(srs, bits, &quotient, gamma, eta)?;
        transcript.append("range check: opening", &opening);

        Ok(Self {
            bits: bit_commitments,
            quotient: quotient_commitment,
            bit_values,
            quotient_value,
            opening,
        })
    }

    /// Verifies that every value of the slice `ṽ` is in `[0, 2^ℓ)`, with `ℓ = ell ≤ MAX_BITS`.
    pub fn verify(
        &self,
        vk: &VerifierKey,
        v: SliceHandle,
        ell: usize,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        let reject = Err(Error::Rejected("range check"));
        if ell > MAX_BITS || self.bits.len() != ell || self.bit_values.len() != ell {
            return reject;
        }

        // 1. Σᵢ 2ⁱ [bᵢ] = ṽ, by Horner's rule.
        let sum = self
            .bits
            .iter()
            .rev()
            .fold(G1Projective::zero(), |acc, bit| acc.double() + bit);
        if sum != v.0 {
            return reject;
        }

        // 2. Σᵢ ρⁱ yᵢ(yᵢ − 1) = Z_H(γ) · y_q.
        let rho = challenge_rho(transcript, v, ell, &self.bits);
        let gamma = challenge_gamma(transcript, self.quotient);
        let eta = challenge_eta(transcript, &self.bit_values, self.quotient_value);
        let bit_check = self
            .bit_values
            .iter()
            .rev()
            .fold(Fr::zero(), |acc, y| acc * rho + *y * (*y - Fr::ONE));
        if bit_check != vk.domain().evaluate_vanishing_polynomial(gamma) * self.quotient_value {
            return reject;
        }

        // 3. e(C − Y·[1]₁ + γ·W, [1]₂) = e(W, [τ]₂), with C and Y combined with powers of η.
        let powers: Vec<Fr> = std::iter::successors(Some(Fr::ONE), |p| Some(*p * eta))
            .take(ell + 1)
            .collect();
        let mut points = self.bits.clone();
        points.push(self.quotient);
        let combined =
            G1Projective::msm_unchecked(&G1Projective::normalize_batch(&points), &powers);
        let value: Fr = self
            .bit_values
            .iter()
            .chain([&self.quotient_value])
            .zip(&powers)
            .map(|(y, p)| *y * p)
            .sum();
        let check = Bls12_381::multi_pairing(
            [
                combined - G1Projective::generator() * value + self.opening * gamma,
                -self.opening,
            ],
            [G2Projective::generator(), G2Projective::from(vk.tau)],
        );
        if !check.is_zero() {
            return reject;
        }

        transcript.append("range check: opening", &self.opening);
        Ok(())
    }
}

fn challenge_rho(
    transcript: &mut Transcript,
    v: SliceHandle,
    ell: usize,
    bits: &[G1Projective],
) -> Fr {
    transcript.append("range check: slice", &v);
    transcript.append("range check: ell", &ell);
    transcript.append("range check: bits", bits);
    transcript.challenge("range check: rho")
}

fn challenge_gamma(transcript: &mut Transcript, quotient: G1Projective) -> Fr {
    transcript.append("range check: quotient", &quotient);
    transcript.challenge("range check: gamma")
}

fn challenge_eta(transcript: &mut Transcript, bit_values: &[Fr], quotient_value: Fr) -> Fr {
    transcript.append("range check: bit values", bit_values);
    transcript.append("range check: quotient value", &quotient_value);
    transcript.challenge("range check: eta")
}

/// `q = Σᵢ ρⁱ bᵢ(bᵢ − 1) / Z_H`, on a coset of size `2N`: `bᵢ(bᵢ − 1)` has degree `< 2N`, and on
/// the coset `Z_H(x) = xᴺ − 1` takes only the values `±gᴺ − 1`.
fn bit_quotient(
    domain: &Domain,
    bits: &[DensePolynomial<Fr>],
    rho: Fr,
) -> Result<DensePolynomial<Fr>, Error> {
    let n = domain.size();
    let coset = Domain::new(2 * n)
        .and_then(|domain| domain.get_coset(Fr::GENERATOR))
        .ok_or(Error::Domain(2 * n))?;

    let mut evals = vec![Fr::zero(); 2 * n];
    let mut rho_i = Fr::ONE;
    for bit in bits {
        if !bit.is_zero() {
            let bit_evals = coset.fft(&bit.coeffs);
            evals
                .par_iter_mut()
                .zip(&bit_evals)
                .for_each(|(acc, b)| *acc += rho_i * b * (*b - Fr::ONE));
        }
        rho_i *= rho;
    }

    // The coset's j-th point is g·ωʲ with ω of order 2N, so its N-th power is gᴺ·(−1)ʲ.
    let g_n = Fr::GENERATOR.pow([n as u64]);
    let mut z_inv = [g_n - Fr::ONE, -g_n - Fr::ONE];
    batch_inversion(&mut z_inv);
    evals
        .par_iter_mut()
        .enumerate()
        .for_each(|(j, e)| *e *= z_inv[j % 2]);
    Ok(DensePolynomial::from_coefficients_vec(coset.ifft(&evals)))
}

/// `[F(τ) − F(γ)) / (τ − γ)]₁` for `F = Σᵢ ηⁱ bᵢ + η^ℓ q`.
fn opening(
    srs: &Srs,
    bits: &[DensePolynomial<Fr>],
    quotient: &DensePolynomial<Fr>,
    gamma: Fr,
    eta: Fr,
) -> Result<G1Projective, Error> {
    let len = bits
        .iter()
        .chain([quotient])
        .map(|p| p.coeffs.len())
        .max()
        .unwrap_or(0);
    let mut combined = vec![Fr::zero(); len];
    let mut eta_i = Fr::ONE;
    for p in bits.iter().chain([quotient]) {
        combined
            .par_iter_mut()
            .zip(&p.coeffs)
            .for_each(|(acc, c)| *acc += eta_i * c);
        eta_i *= eta;
    }
    let combined = DensePolynomial::from_coefficients_vec(combined);
    // The remainder of the division is F(γ): dropping it gives (F − F(γ)) / (x − γ).
    srs.commit_g1(&divide_by_linear(&combined, gamma))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handle::Slice;
    use ark_std::test_rng;

    fn slice(srs: &Srs, values: Vec<Fr>) -> CommittedSlice {
        Slice::new(values).commit(srs).unwrap()
    }

    fn prove(srs: &Srs, v: &CommittedSlice, ell: usize) -> Result<RangeCheckProof, Error> {
        RangeCheckProof::prove(srs, v, ell, &mut Transcript::new("test"))
    }

    fn verify(
        proof: &RangeCheckProof,
        srs: &Srs,
        v: &CommittedSlice,
        ell: usize,
    ) -> Result<(), Error> {
        proof.verify(
            &srs.verifier_key(),
            v.handle(),
            ell,
            &mut Transcript::new("test"),
        )
    }

    /// A proof whose bit polynomials are `bits` (not necessarily bits) and whose quotient is 0,
    /// with honest values and opening.
    fn with_zero_quotient(
        srs: &Srs,
        v: &CommittedSlice,
        bits: &[DensePolynomial<Fr>],
    ) -> RangeCheckProof {
        let transcript = &mut Transcript::new("test");
        let commitments: Vec<_> = bits.iter().map(|b| srs.commit_g1(b).unwrap()).collect();
        challenge_rho(transcript, v.handle(), bits.len(), &commitments);
        let quotient = DensePolynomial::zero();
        let gamma = challenge_gamma(transcript, G1Projective::zero());
        let bit_values: Vec<Fr> = bits.iter().map(|b| b.evaluate(&gamma)).collect();
        let eta = challenge_eta(transcript, &bit_values, Fr::zero());
        RangeCheckProof {
            bits: commitments,
            quotient: G1Projective::zero(),
            bit_values,
            quotient_value: Fr::zero(),
            opening: opening(srs, bits, &quotient, gamma, eta).unwrap(),
        }
    }

    #[test]
    fn accepts_values_in_range() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let two = Fr::from(2u64);
        let cases = [
            (vec![], 8),
            (vec![Fr::zero(); 16], 1),
            // Shorter than the domain: zero on the last rows.
            ((1..=10u64).map(Fr::from).collect(), 4),
            (
                vec![Fr::from(u64::MAX), Fr::zero(), Fr::from(1u64 << 63)],
                64,
            ),
            (vec![two.pow([200]) - Fr::ONE, two.pow([150])], 200),
        ];

        for (values, ell) in cases {
            let v = slice(&srs, values);
            let proof = prove(&srs, &v, ell).unwrap();
            assert_eq!(verify(&proof, &srs, &v, ell), Ok(()));
        }
    }

    #[test]
    fn prover_refuses_values_out_of_range() {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let cases = [
            (-Fr::ONE, 64),
            (Fr::from(u64::MAX) + Fr::ONE, 64),
            (Fr::from(16u64), 4),
            // 2^255 is above the field order.
            (Fr::ONE, MAX_BITS + 1),
        ];

        for (value, ell) in cases {
            let v = slice(&srs, vec![Fr::from(3u64), value]);
            assert_eq!(
                prove(&srs, &v, ell),
                Err(Error::InvalidWitness("range check"))
            );
        }
    }

    #[test]
    fn each_check_is_needed() {
        let ell = 8;
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let reject = Err(Error::Rejected("range check"));
        // −1 on row 0: not in range.
        let v = slice(&srs, vec![-Fr::ONE]);
        let not_bits: Vec<DensePolynomial<Fr>> = std::iter::once(v.polynomial().clone())
            .chain(std::iter::repeat_n(DensePolynomial::zero(), ell - 1))
            .collect();

        // 1. The bits of 5 (real bits), in a proof for ṽ: only the recomposition catches it.
        let five: Vec<DensePolynomial<Fr>> = (0..ell)
            .map(|i| {
                let bit = Fr::from((5u64 >> i) & 1);
                DensePolynomial::from_coefficients_vec(srs.domain().ifft(&[bit]))
            })
            .collect();
        let transcript = &mut Transcript::new("test");
        let forged = RangeCheckProof::prove_bits(&srs, v.handle(), &five, transcript).unwrap();
        assert_eq!(verify(&forged, &srs, &v, ell), reject);

        // 2. b₀ = v, not bits, with q = 0 and honest values: only the bit check catches it.
        assert_eq!(
            verify(&with_zero_quotient(&srs, &v, &not_bits), &srs, &v, ell),
            reject
        );

        // 3. The same, with values chosen after η so that the bit check holds and the combination
        //    Σ ηⁱ yᵢ + η^ℓ y_q is unchanged: rejected because η depends on the values.
        let mut forged = with_zero_quotient(&srs, &v, &not_bits);
        let transcript = &mut Transcript::new("test");
        let rho = challenge_rho(transcript, v.handle(), ell, &forged.bits);
        let gamma = challenge_gamma(transcript, forged.quotient);
        let eta = challenge_eta(transcript, &forged.bit_values, forged.quotient_value);
        let (t0, z, eta_q) = (
            forged.bit_values[0],
            srs.domain().evaluate_vanishing_polynomial(gamma),
            eta.pow([ell as u64]),
        );
        // y₁ = c, y_q = (t0 − y₀ − η·c) / η^ℓ, and y₀(y₀ − 1) + ρ·c(c − 1) = z·y_q: a quadratic
        // y₀² + B·y₀ + C = 0 in y₀; try values of c until it has a root.
        let (y0, c) = (0..64u64)
            .map(Fr::from)
            .find_map(|c| {
                let k = z / eta_q;
                let b = k - Fr::ONE;
                let cc = rho * c * (c - Fr::ONE) - k * (t0 - eta * c);
                let root = (b * b - cc.double().double()).sqrt()?;
                Some(((root - b) * Fr::from(2u64).inverse()?, c))
            })
            .unwrap();
        forged.bit_values[0] = y0;
        forged.bit_values[1] = c;
        forged.quotient_value = (t0 - y0 - eta * c) / eta_q;
        assert_eq!(verify(&forged, &srs, &v, ell), reject);
    }
}
