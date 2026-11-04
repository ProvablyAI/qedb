//! Intersection test `Ĩ = S̃₁ ∩ … ∩ S̃ₖ` (Fig. 5, Fig. 8).
//!
//! `I = ∩ Sᵢ` if and only if `I ⊆ Sᵢ` for every `i` and the differences `Dᵢ = Sᵢ ∖ I` have no
//! common row, i.e. `gcd(P_{D₁}, …, P_{Dₖ}) = 1`. The prover sends `[P_{Dᵢ}(τ)]₂` and Bézout
//! coefficients `[qᵢ(τ)]₁` with `Σ qᵢ · P_{Dᵢ} = 1`. The verifier checks
//!
//! 1. `e(Ĩ, [P_{Dᵢ}]₂) = e(S̃ᵢ, [1]₂)` for every `i`: `P_I · P_{Dᵢ} = P_{Sᵢ}`;
//! 2. `Σᵢ e([qᵢ]₁, [P_{Dᵢ}]₂) = e([1]₁, [1]₂)`: `Σ qᵢ · P_{Dᵢ} = 1`;
//!
//! batched with a challenge `ρ` as `Σᵢ e(ρⁱĨ + [qᵢ]₁, [P_{Dᵢ}]₂) = e([1]₁ + Σᵢ ρⁱS̃ᵢ, [1]₂)`.
//! The proof must have exactly one difference and one coefficient per set: an extra pair
//! `([1]₁, [1]₂)` would satisfy the second equation for any sets.

use super::divide_exact;
use crate::Error;
use crate::handle::{CommittedSet, Set, SetHandle};
use crate::setup::{Domain, Srs};
use crate::transcript::Transcript;
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::PrimeGroup;
use ark_ec::pairing::Pairing;
use ark_ff::{Field, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::*;

/// Proof that a set is the intersection of other sets.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct IntersectionProof {
    /// `[P_{Dᵢ}(τ)]₂` with `Dᵢ = Sᵢ ∖ I`.
    pub(crate) differences_g2: Vec<G2Projective>,
    /// `[qᵢ(τ)]₁` with `Σ qᵢ · P_{Dᵢ} = 1`.
    pub(crate) bezout_g1: Vec<G1Projective>,
}

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

        let domain = srs.domain();
        let differences: Vec<Set> = sets
            .iter()
            .map(|set| {
                Set::new(
                    set.set()
                        .rows()
                        .iter()
                        .copied()
                        .filter(|row| rows.binary_search(row).is_err()),
                )
            })
            .collect();
        let polynomials = differences
            .par_iter()
            .map(|difference| difference.characteristic(domain))
            .collect::<Result<Vec<_>, _>>()?;
        let bezout = bezout_coefficients(domain, &differences, &polynomials)?;

        let proof = Self {
            differences_g2: polynomials
                .par_iter()
                .map(|p| srs.commit_g2(p))
                .collect::<Result<_, _>>()?,
            bezout_g1: bezout
                .par_iter()
                .map(|q| srs.commit_g1(q))
                .collect::<Result<_, _>>()?,
        };
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
        let k = sets.len();
        if k == 0 || self.differences_g2.len() != k || self.bezout_g1.len() != k {
            return Err(Error::Rejected("intersection test"));
        }

        let rho = self.challenge(sets, intersection, transcript);
        let mut g1 = Vec::with_capacity(k + 1);
        let mut g2 = Vec::with_capacity(k + 1);
        let mut rho_i = Fr::ONE;
        let mut rhs = G1Projective::generator();
        for ((set, difference), q) in sets.iter().zip(&self.differences_g2).zip(&self.bezout_g1) {
            rho_i *= rho;
            g1.push(intersection.0 * rho_i + q);
            g2.push(*difference);
            rhs += set.0 * rho_i;
        }
        g1.push(-rhs);
        g2.push(G2Projective::generator());

        if !Bls12_381::multi_pairing(g1, g2).is_zero() {
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

/// Bézout coefficients `qᵢ` with `Σ qᵢ · P_{Dᵢ} = 1`, for sets `Dᵢ` with no common row.
///
/// With `V = ∪ Dᵢ` and `Q = P_{H∖V}`, every row of `V` is assigned to one set that misses it, and
/// `Cᵢ` is the polynomial of degree `< N` equal to `Q` on the rows assigned to `i` and to `0` on
/// the other rows of `H`. `Cᵢ` vanishes on `H ∖ V` and on `Dᵢ`, so `qᵢ = Cᵢ / (Q · P_{Dᵢ})` is a
/// polynomial, and `Σ qᵢ · P_{Dᵢ} = (Σ Cᵢ) / Q = 1`: `Σ Cᵢ` and `Q` agree on `H` and have degree
/// `< N`.
fn bezout_coefficients(
    domain: &Domain,
    differences: &[Set],
    polynomials: &[DensePolynomial<Fr>],
) -> Result<Vec<DensePolynomial<Fr>>, Error> {
    // An empty Dᵢ has P_{Dᵢ} = 1: qᵢ = 1, and 0 for the other sets.
    if let Some(empty) = differences.iter().position(|d| d.rows().is_empty()) {
        return Ok((0..differences.len())
            .map(|i| {
                let q = if i == empty { vec![Fr::ONE] } else { vec![] };
                DensePolynomial::from_coefficients_vec(q)
            })
            .collect());
    }

    let n = domain.size();
    let mut assigned = vec![Vec::new(); differences.len()];
    let mut in_union = vec![false; n];
    for &row in differences.iter().flat_map(Set::rows) {
        if !in_union[row] {
            in_union[row] = true;
            let i = differences
                .iter()
                .position(|d| d.rows().binary_search(&row).is_err())
                .ok_or(Error::InvalidWitness("intersection test"))?;
            assigned[i].push(row);
        }
    }

    let q = Set::new((0..n).filter(|&row| !in_union[row])).characteristic(domain)?;
    let q_evals = domain.fft(&q.coeffs);
    assigned
        .par_iter()
        .zip(polynomials)
        .map(|(rows, p)| {
            let mut c = vec![Fr::zero(); n];
            for &row in rows {
                c[row] = q_evals[row];
            }
            let c = DensePolynomial::from_coefficients_vec(domain.ifft(&c));
            divide_exact(&c, &(&q * p))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let forged = IntersectionProof {
            differences_g2: [&[0, 3][..], &[3, 4]]
                .iter()
                .map(|rows| srs.commit_g2(set(&srs, rows).polynomial()).unwrap())
                .collect(),
            bezout_g1: vec![G1Projective::zero(); 2],
        };

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
        proof.differences_g2.push(G2Projective::generator());
        proof.bezout_g1.push(G1Projective::generator());

        assert_eq!(
            verify(&proof, &[&a, &b], &set(&srs, &[2, 3])),
            Err(Error::Rejected("intersection test"))
        );
    }
}
