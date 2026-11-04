//! Primitives of qedb ([ePrint 2025/1408](https://eprint.iacr.org/2025/1408)), over BLS12-381.

#![warn(missing_docs)]

pub mod setup;

use std::fmt;

/// Errors returned by the primitives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// No evaluation domain holds the requested number of rows.
    Domain(usize),
    /// A polynomial has more coefficients than the SRS has powers.
    TooManyCoefficients {
        /// Coefficients in the polynomial.
        len: usize,
        /// Powers in the SRS.
        max: usize,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Domain(n) => write!(f, "no evaluation domain of at least {n} rows"),
            Self::TooManyCoefficients { len, max } => {
                write!(
                    f,
                    "polynomial has {len} coefficients, the SRS supports {max}"
                )
            }
        }
    }
}

impl std::error::Error for Error {}
