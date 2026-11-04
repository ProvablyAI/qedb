//! Set and slice handles (Fig. 8).
//!
//! The prover holds a [`Set`] of rows or a [`Slice`] of values; the verifier only sees their
//! handles, [`SetHandle`] and [`SliceHandle`]. Row `i` is the domain element `ωⁱ`.

use crate::Error;
use crate::setup::{Domain, Srs};
use ark_bls12_381::{Fr, G1Projective};
use ark_ff::{Field, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use std::ops::{Add, Mul, Neg, Sub};

/// Up to this many roots, [`product_of_roots`] multiplies the factors one at a time instead of
/// splitting further: for small polynomials this is faster than an FFT multiplication.
const NAIVE_PRODUCT_ROOTS: usize = 64;

/// A set of rows `S`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Set(Vec<usize>);

impl Set {
    /// The set of the given rows; repeated rows are kept once.
    pub fn new(rows: impl IntoIterator<Item = usize>) -> Self {
        let mut rows: Vec<usize> = rows.into_iter().collect();
        rows.sort_unstable();
        rows.dedup();
        Self(rows)
    }

    /// The rows, in increasing order.
    pub fn rows(&self) -> &[usize] {
        &self.0
    }

    /// The characteristic polynomial `P_S(x) = ∏_{i ∈ S} (x − ωⁱ)`.
    pub fn characteristic(&self, domain: &Domain) -> Result<DensePolynomial<Fr>, Error> {
        if let Some(&row) = self.0.last().filter(|&&row| row >= domain.size()) {
            return Err(Error::RowOutOfDomain {
                row,
                size: domain.size(),
            });
        }
        let roots: Vec<Fr> = self.0.iter().map(|&i| domain.element(i)).collect();
        Ok(product_of_roots(&roots))
    }

    /// The accumulator `[P_S(τ)]₁`.
    pub fn handle(&self, srs: &Srs) -> Result<SetHandle, Error> {
        let p = self.characteristic(srs.domain())?;
        Ok(SetHandle(srs.commit_g1(&p)?))
    }
}

/// `∏ (x − r)` over `roots`, as a balanced product tree.
fn product_of_roots(roots: &[Fr]) -> DensePolynomial<Fr> {
    if roots.len() <= NAIVE_PRODUCT_ROOTS {
        let mut coeffs = vec![Fr::ONE];
        for r in roots {
            // Multiply by (x − r): c'ᵢ = cᵢ₋₁ − r·cᵢ.
            coeffs.push(Fr::zero());
            for i in (1..coeffs.len()).rev() {
                coeffs[i] = coeffs[i - 1] - *r * coeffs[i];
            }
            coeffs[0] *= -*r;
        }
        return DensePolynomial::from_coefficients_vec(coeffs);
    }
    let (left, right) = roots.split_at(roots.len() / 2);
    let (left, right) = rayon::join(|| product_of_roots(left), || product_of_roots(right));
    &left * &right
}

/// A slice `v`: `vᵢ` on row `i`, `0` on the rows after the last value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slice(Vec<Fr>);

impl Slice {
    /// The slice with the given values on rows `0, 1, …`.
    pub const fn new(values: Vec<Fr>) -> Self {
        Self(values)
    }

    /// The values, starting from row `0`.
    pub fn values(&self) -> &[Fr] {
        &self.0
    }

    /// The polynomial `v(x) = Σᵢ vᵢ λᵢ(x)`, with `λᵢ` the Lagrange basis of the domain.
    pub fn polynomial(&self, domain: &Domain) -> Result<DensePolynomial<Fr>, Error> {
        if self.0.len() > domain.size() {
            return Err(Error::RowOutOfDomain {
                row: self.0.len() - 1,
                size: domain.size(),
            });
        }
        Ok(DensePolynomial::from_coefficients_vec(domain.ifft(&self.0)))
    }

    /// The commitment `[v(τ)]₁`.
    pub fn handle(&self, srs: &Srs) -> Result<SliceHandle, Error> {
        let p = self.polynomial(srs.domain())?;
        Ok(SliceHandle(srs.commit_g1(&p)?))
    }
}

/// Handle to a set: the accumulator `[P_S(τ)]₁`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SetHandle(pub(crate) G1Projective);

/// Handle to a slice: the commitment `[v(τ)]₁`.
///
/// Slice handles are homomorphic, so the verifier computes `α·u + w` locally (Fig. 8).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SliceHandle(pub(crate) G1Projective);

impl Add for SliceHandle {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Sub for SliceHandle {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl Neg for SliceHandle {
    type Output = Self;

    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl Mul<Fr> for SliceHandle {
    type Output = Self;

    fn mul(self, alpha: Fr) -> Self {
        Self(self.0 * alpha)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;
    use ark_poly::Polynomial;
    use ark_std::test_rng;

    #[test]
    fn characteristic_vanishes_exactly_on_the_set() {
        let domain = Domain::new(256).unwrap();
        // Enough rows to use the product tree, not only the naive product.
        let set = Set::new((0..256).filter(|i| i % 3 != 0));

        let p = set.characteristic(&domain).unwrap();

        assert_eq!(p.degree(), set.rows().len());
        for (i, w) in domain.elements().enumerate() {
            assert_eq!(p.evaluate(&w).is_zero(), set.rows().contains(&i));
        }
    }

    #[test]
    fn slice_handles_are_homomorphic() {
        let rng = &mut test_rng();
        let srs = Srs::setup(16, rng).unwrap();
        let u: Vec<Fr> = (0..16).map(|_| Fr::rand(rng)).collect();
        // Shorter than u: zero on the last rows.
        let w: Vec<Fr> = (0..5).map(|_| Fr::rand(rng)).collect();
        let alpha = Fr::rand(rng);
        let combined = (0..16)
            .map(|i| alpha * u[i] + w.get(i).copied().unwrap_or_default())
            .collect();

        let u_handle = Slice::new(u).handle(&srs).unwrap();
        let w_handle = Slice::new(w).handle(&srs).unwrap();

        assert_eq!(
            Slice::new(combined).handle(&srs).unwrap(),
            u_handle * alpha + w_handle
        );
    }

    #[test]
    fn rejects_rows_outside_the_domain() {
        let srs = Srs::setup(8, &mut test_rng()).unwrap();
        let error = Error::RowOutOfDomain { row: 8, size: 8 };

        assert_eq!(Set::new([1, 8]).handle(&srs), Err(error.clone()));
        assert_eq!(Slice::new(vec![Fr::ONE; 9]).handle(&srs), Err(error));
    }
}
