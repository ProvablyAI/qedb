//! Set and slice handles (Fig. 8).
//!
//! The prover holds a [`Set`] of rows or a [`Slice`] of values; the verifier only sees their
//! handles, [`SetHandle`] and [`SliceHandle`]. Row `i` is the domain element `ωⁱ`.

use crate::Error;
use crate::setup::{Domain, Srs, VerifierKey};
use ark_bls12_381::{Fr, G1Projective, G2Projective};
use ark_ec::PrimeGroup;
use ark_ff::{Field, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::*;
use std::ops::{Add, Mul, Neg, Sub};
use std::sync::OnceLock;

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

    /// The rows of `self` that are not in `other`.
    pub fn difference(&self, other: &Self) -> Self {
        let rows = self.0.iter().copied();
        Self(
            rows.filter(|row| other.0.binary_search(row).is_err())
                .collect(),
        )
    }

    /// The characteristic polynomial `P_S(x) = ∏_{i ∈ S} (x − ωⁱ)`.
    pub fn characteristic(&self, domain: &Domain) -> Result<DensePolynomial<Fr>, Error> {
        if let Some(&row) = self.0.last().filter(|&&row| row >= domain.size()) {
            return Err(Error::RowOutOfDomain {
                row,
                size: domain.size(),
            });
        }
        let roots: Vec<Fr> = self.0.par_iter().map(|&i| domain.element(i)).collect();
        Ok(product_of_roots(&roots))
    }

    /// Commits to the set: its characteristic polynomial and the accumulator `[P_S(τ)]₁`.
    pub fn commit(self, srs: &Srs) -> Result<CommittedSet, Error> {
        let polynomial = self.characteristic(srs.domain())?;
        let handle = SetHandle(srs.commit_g1(&polynomial)?);
        Ok(CommittedSet {
            set: self,
            polynomial,
            handle,
            handle_g2: OnceLock::new(),
        })
    }
}

/// A set with its characteristic polynomial and handle, as held by the prover.
#[derive(Clone, Debug)]
pub struct CommittedSet {
    set: Set,
    polynomial: DensePolynomial<Fr>,
    handle: SetHandle,
    handle_g2: OnceLock<G2Projective>,
}

impl CommittedSet {
    /// The set `S`.
    pub const fn set(&self) -> &Set {
        &self.set
    }

    /// The characteristic polynomial `P_S`.
    pub const fn polynomial(&self) -> &DensePolynomial<Fr> {
        &self.polynomial
    }

    /// The handle `S̃`.
    pub const fn handle(&self) -> SetHandle {
        self.handle
    }

    /// `[P_S(τ)]₂`, computed on first use: several tests on the same set send it.
    pub(crate) fn handle_g2(&self, srs: &Srs) -> Result<G2Projective, Error> {
        if let Some(&g2) = self.handle_g2.get() {
            return Ok(g2);
        }
        let g2 = srs.commit_g2(&self.polynomial)?;
        Ok(*self.handle_g2.get_or_init(|| g2))
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

    /// Commits to the slice: its polynomial and the commitment `[v(τ)]₁`, from the values in the
    /// Lagrange basis.
    pub fn commit(self, srs: &Srs) -> Result<CommittedSlice, Error> {
        let polynomial = self.polynomial(srs.domain())?;
        let handle = SliceHandle(srs.commit_lagrange(&self.0)?);
        Ok(CommittedSlice {
            slice: self,
            polynomial,
            handle,
        })
    }
}

/// A slice with its polynomial and handle, as held by the prover.
#[derive(Clone, Debug)]
pub struct CommittedSlice {
    slice: Slice,
    polynomial: DensePolynomial<Fr>,
    handle: SliceHandle,
}

impl CommittedSlice {
    /// The slice `v`.
    pub const fn slice(&self) -> &Slice {
        &self.slice
    }

    /// The polynomial `v(x)`.
    pub const fn polynomial(&self) -> &DensePolynomial<Fr> {
        &self.polynomial
    }

    /// The handle `ṽ`.
    pub const fn handle(&self) -> SliceHandle {
        self.handle
    }
}

/// `α·v`, with the handle `α·ṽ` computed homomorphically.
impl Mul<Fr> for &CommittedSlice {
    type Output = CommittedSlice;

    fn mul(self, alpha: Fr) -> CommittedSlice {
        CommittedSlice {
            slice: Slice(self.slice.values().iter().map(|x| *x * alpha).collect()),
            polynomial: &self.polynomial * alpha,
            handle: self.handle * alpha,
        }
    }
}

/// `−v`, with the handle `−ṽ` computed homomorphically.
impl Neg for &CommittedSlice {
    type Output = CommittedSlice;

    fn neg(self) -> CommittedSlice {
        CommittedSlice {
            slice: Slice(self.slice.values().iter().map(|x| -*x).collect()),
            polynomial: -self.polynomial.clone(),
            handle: -self.handle,
        }
    }
}

/// `u − v`, with the handle `ũ − ṽ` computed homomorphically.
impl Sub for &CommittedSlice {
    type Output = CommittedSlice;

    fn sub(self, rhs: Self) -> CommittedSlice {
        let (u, v) = (self.slice.values(), rhs.slice.values());
        let values = (0..u.len().max(v.len()))
            .map(|i| u.get(i).copied().unwrap_or_default() - v.get(i).copied().unwrap_or_default())
            .collect();
        CommittedSlice {
            slice: Slice(values),
            polynomial: &self.polynomial - &rhs.polynomial,
            handle: self.handle - rhs.handle,
        }
    }
}

/// The public handles of a table's indexing (Table 2): its rows `∗ = {0, …, n − 1}` and the
/// all-ones slice `1` on them.
#[derive(Clone, Debug)]
pub struct Universe {
    rows: CommittedSet,
    ones: CommittedSlice,
}

impl Universe {
    /// The universe of a table of `n` rows.
    pub fn new(srs: &Srs, n: usize) -> Result<Self, Error> {
        Ok(Self {
            rows: Set::new(0..n).commit(srs)?,
            ones: Slice::new(vec![Fr::ONE; n]).commit(srs)?,
        })
    }

    /// The rows `∗`.
    pub const fn rows(&self) -> &CommittedSet {
        &self.rows
    }

    /// The all-ones slice `1`.
    pub const fn ones(&self) -> &CommittedSlice {
        &self.ones
    }

    /// The handles of `∗` and `1`.
    pub const fn handle(&self) -> UniverseHandle {
        UniverseHandle {
            rows: self.rows.handle(),
            ones: self.ones.handle(),
        }
    }

    /// The universe of every row of the domain `H`, from closed forms: `P_H = xᴺ − 1`, and the
    /// all-ones slice is the constant `1`.
    pub(crate) fn domain(srs: &Srs) -> Self {
        let n = srs.domain().size();
        let mut z_h = vec![Fr::zero(); n + 1];
        z_h[0] = -Fr::ONE;
        z_h[n] = Fr::ONE;
        let one = G1Projective::from(srs.g1()[0]);
        Self {
            rows: CommittedSet {
                set: Set((0..n).collect()),
                polynomial: DensePolynomial::from_coefficients_vec(z_h),
                handle: SetHandle(srs.g1()[n] - one),
                handle_g2: OnceLock::new(),
            },
            ones: CommittedSlice {
                slice: Slice(vec![Fr::ONE; n]),
                polynomial: DensePolynomial::from_coefficients_vec(vec![Fr::ONE]),
                handle: SliceHandle(one),
            },
        }
    }
}

/// Handles of a [`Universe`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct UniverseHandle {
    /// The rows `∗`.
    pub rows: SetHandle,
    /// The all-ones slice `1`.
    pub ones: SliceHandle,
}

impl UniverseHandle {
    /// The handles of [`Universe::domain`], from the verifier key.
    pub(crate) fn domain(vk: &VerifierKey) -> Self {
        let one = G1Projective::generator();
        Self {
            rows: SetHandle(vk.tau_n_g1 - one),
            ones: SliceHandle(one),
        }
    }
}

/// Handle to a set: the accumulator `[P_S(τ)]₁`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct SetHandle(pub(crate) G1Projective);

/// Handle to a slice: the commitment `[v(τ)]₁`.
///
/// Slice handles are homomorphic, so the verifier computes `α·u + w` locally (Fig. 8).
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
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

        let u_handle = Slice::new(u).commit(&srs).unwrap().handle();
        let w_handle = Slice::new(w).commit(&srs).unwrap().handle();

        assert_eq!(
            Slice::new(combined).commit(&srs).unwrap().handle(),
            u_handle * alpha + w_handle
        );
    }

    #[test]
    fn rejects_rows_outside_the_domain() {
        let srs = Srs::setup(8, &mut test_rng()).unwrap();
        let error = Error::RowOutOfDomain { row: 8, size: 8 };

        assert_eq!(Set::new([1, 8]).commit(&srs).err(), Some(error.clone()));
        assert_eq!(Slice::new(vec![Fr::ONE; 9]).commit(&srs).err(), Some(error));
    }
}
