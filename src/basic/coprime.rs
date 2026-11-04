//! Proof that sets `D₁, …, Dₖ` have no common row, shared by the intersection and union tests.
//!
//! The prover sends `[P_{Dᵢ}(τ)]₂` and Bézout coefficients `[qᵢ(τ)]₁` with `Σ qᵢ · P_{Dᵢ} = 1`,
//! which exist if and only if `gcd(P_{D₁}, …, P_{Dₖ}) = 1`. Each test ties every `Dᵢ` to its
//! sets with an equation `e(aᵢ, [P_{Dᵢ}]₂) = e(tᵢ, [1]₂)`. The verifier checks these and
//! `Σᵢ e([qᵢ]₁, [P_{Dᵢ}]₂) = e([1]₁, [1]₂)`, batched with a challenge `ρ` as
//! `Σᵢ e(ρⁱaᵢ + [qᵢ]₁, [P_{Dᵢ}]₂) = e([1]₁ + Σᵢ ρⁱtᵢ, [1]₂)`.
//!
//! The proof must have exactly one `Dᵢ` and one `qᵢ` per equation: an extra pair `([1]₁, [1]₂)`
//! would satisfy the Bézout equation for any sets.

use super::divide_exact;
use crate::Error;
use crate::handle::Set;
use crate::setup::{Domain, Srs};
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::PrimeGroup;
use ark_ec::pairing::Pairing;
use ark_ff::{Field, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CoprimeProof {
    /// `[P_{Dᵢ}(τ)]₂`.
    pub sets_g2: Vec<G2Projective>,
    /// `[qᵢ(τ)]₁` with `Σ qᵢ · P_{Dᵢ} = 1`.
    pub bezout_g1: Vec<G1Projective>,
}

impl CoprimeProof {
    /// Proves that `sets` have no common row; `test` names the calling test in errors.
    pub fn prove(srs: &Srs, sets: &[Set], test: &'static str) -> Result<Self, Error> {
        let domain = srs.domain();
        let polynomials = sets
            .par_iter()
            .map(|set| set.characteristic(domain))
            .collect::<Result<Vec<_>, _>>()?;
        let bezout = bezout_coefficients(domain, sets, &polynomials, test)?;

        Ok(Self {
            sets_g2: polynomials
                .par_iter()
                .map(|p| srs.commit_g2(p))
                .collect::<Result<_, _>>()?,
            bezout_g1: bezout
                .par_iter()
                .map(|q| srs.commit_g1(q))
                .collect::<Result<_, _>>()?,
        })
    }

    /// Checks `e(aᵢ, [P_{Dᵢ}]₂) = e(tᵢ, [1]₂)` for the pairs `(aᵢ, tᵢ)`, and the Bézout equation.
    pub fn verify(&self, pairs: &[(G1Projective, G1Projective)], rho: Fr) -> bool {
        let k = pairs.len();
        if k == 0 || self.sets_g2.len() != k || self.bezout_g1.len() != k {
            return false;
        }

        let mut g1 = Vec::with_capacity(k + 1);
        let mut g2 = Vec::with_capacity(k + 1);
        let mut rho_i = Fr::ONE;
        let mut rhs = G1Projective::generator();
        for (((a, t), set), q) in pairs.iter().zip(&self.sets_g2).zip(&self.bezout_g1) {
            rho_i *= rho;
            g1.push(*a * rho_i + q);
            g2.push(*set);
            rhs += *t * rho_i;
        }
        g1.push(-rhs);
        g2.push(G2Projective::generator());

        Bls12_381::multi_pairing(g1, g2).is_zero()
    }
}

/// Bézout coefficients `qᵢ` with `Σ qᵢ · P_{Dᵢ} = 1`, for sets `Dᵢ` with no common row.
///
/// With `V = ∪ Dᵢ` and `Q = P_{H∖V}`, every row of `V` is assigned to one set that misses it, and
/// `Fᵢ` is the polynomial of degree `< N` equal to `Q` on the rows assigned to `i` and to `0` on
/// the other rows of `H`. `Fᵢ` vanishes on `H ∖ V` and on `Dᵢ`, so `qᵢ = Fᵢ / (Q · P_{Dᵢ})` is a
/// polynomial, and `Σ qᵢ · P_{Dᵢ} = (Σ Fᵢ) / Q = 1`: `Σ Fᵢ` and `Q` agree on `H` and have degree
/// `< N`.
fn bezout_coefficients(
    domain: &Domain,
    sets: &[Set],
    polynomials: &[DensePolynomial<Fr>],
    test: &'static str,
) -> Result<Vec<DensePolynomial<Fr>>, Error> {
    // An empty Dᵢ has P_{Dᵢ} = 1: qᵢ = 1, and 0 for the other sets.
    if let Some(empty) = sets.iter().position(|set| set.rows().is_empty()) {
        return Ok((0..sets.len())
            .map(|i| {
                let q = if i == empty { vec![Fr::ONE] } else { vec![] };
                DensePolynomial::from_coefficients_vec(q)
            })
            .collect());
    }

    let n = domain.size();
    let mut assigned = vec![Vec::new(); sets.len()];
    let mut in_union = vec![false; n];
    for &row in sets.iter().flat_map(Set::rows) {
        if !in_union[row] {
            in_union[row] = true;
            let i = sets
                .iter()
                .position(|set| set.rows().binary_search(&row).is_err())
                .ok_or(Error::InvalidWitness(test))?;
            assigned[i].push(row);
        }
    }

    let q = Set::new((0..n).filter(|&row| !in_union[row])).characteristic(domain)?;
    let q_evals = domain.fft(&q.coeffs);
    assigned
        .par_iter()
        .zip(polynomials)
        .map(|(rows, p)| {
            let mut f = vec![Fr::zero(); n];
            for &row in rows {
                f[row] = q_evals[row];
            }
            let f = DensePolynomial::from_coefficients_vec(domain.ifft(&f));
            divide_exact(&f, &(&q * p))
        })
        .collect()
}
