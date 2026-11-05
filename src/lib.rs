//! Primitives of qedb ([ePrint 2025/1408](https://eprint.iacr.org/2025/1408)), over BLS12-381.

#![warn(missing_docs)]

pub mod basic;
pub mod derived;
mod error;
pub mod handle;
pub mod setup;
pub mod transcript;

pub use error::Error;
