//! Derived tests of the paper's model (Table 2), composed from the basic tests.

pub mod eq_set;
pub mod nullifying;
pub mod range_check;
pub mod sign_check;
pub mod sum_check;

use ark_bls12_381::Fr;
use ark_ff::PrimeField;

/// Whether `x` encodes a negative integer: `x > (p − 1) / 2`.
fn is_negative(x: Fr) -> bool {
    x.into_bigint() > Fr::MODULUS_MINUS_ONE_DIV_TWO
}
