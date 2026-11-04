//! Basic tests of the paper's model (Fig. 8).

pub mod complement;
mod coprime;
pub mod inner_product;
pub mod intersection;
pub mod subset;
pub mod union;
pub mod zero_test;

use crate::Error;
use crate::setup::Domain;
use ark_bls12_381::Fr;
use ark_ff::{FftField, batch_inversion};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use rayon::prelude::*;

/// `v / p` for `p` dividing `v`: two FFTs on a coset, a point-wise division and an inverse FFT.
///
/// `p` does not vanish on the coset: its roots are in `H`, and the coset `g·H'`, with `g` the
/// generator of the multiplicative group, contains no element of a subgroup of order `2ᵏ`.
pub(crate) fn divide_exact(
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
