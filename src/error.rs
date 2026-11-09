//! Errors returned by the primitives.

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
    /// The powers of an SRS do not start from the generators `[1]₁` and `[1]₂`.
    Generators,
    /// A row is outside the evaluation domain.
    RowOutOfDomain {
        /// The row.
        row: usize,
        /// Rows in the domain.
        size: usize,
    },
    /// The prover's witness does not satisfy the named test.
    InvalidWitness(&'static str),
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
            Self::Generators => write!(f, "the powers do not start from the generators"),
            Self::RowOutOfDomain { row, size } => {
                write!(f, "row {row} is outside the domain of {size} rows")
            }
            Self::InvalidWitness(test) => write!(f, "{test}: invalid witness"),
            Self::Rejected(test) => write!(f, "{test}: verification failed"),
        }
    }
}

impl std::error::Error for Error {}
