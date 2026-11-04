//! Primitives of qedb ([ePrint 2025/1408](https://eprint.iacr.org/2025/1408)), over BLS12-381.

#![warn(missing_docs)]

pub mod basic;
pub mod handle;
pub mod setup;
pub mod transcript;

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
    /// A row is outside the evaluation domain.
    RowOutOfDomain {
        /// The row.
        row: usize,
        /// Rows in the domain.
        size: usize,
    },
    /// The prover's slice is not zero on a row where it must be.
    NotZero {
        /// The row.
        row: usize,
    },
    /// The verifier rejected a proof of the named test.
    Rejected(&'static str),
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
            Self::RowOutOfDomain { row, size } => {
                write!(f, "row {row} is outside the domain of {size} rows")
            }
            Self::NotZero { row } => write!(f, "the slice is not zero on row {row}"),
            Self::Rejected(test) => write!(f, "{test}: verification failed"),
        }
    }
}

impl std::error::Error for Error {}
