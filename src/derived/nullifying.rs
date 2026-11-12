//! Nullifying test `ũ = ṽ[X̃₀ → 0]` (Sec. 6.1, Table 2): `u` is `0` on `X₀` and equal to `v` on
//! the other rows of the universe `∗`.
//!
//! The prover sends `X̄₀ = ∗ ∖ X₀`, and the verifier checks
//!
//! 1. the complement test `X̄₀ = ∗ ∖ X₀`;
//! 2. the zero test `u[X₀] = 0`;
//! 3. the zero test `(u − v)[X̄₀] = 0`.
//!
//! `∗` is the universe handle given by the caller (for a table, its rows): rows outside `∗` are
//! not checked.

use crate::Error;
use crate::basic::complement::ComplementProof;
use crate::basic::zero_test::ZeroTestProof;
use crate::handle::{
    CommittedSet, CommittedSlice, SetHandle, SliceHandle, Universe, UniverseHandle,
};
use crate::setup::Srs;
use crate::transcript::Transcript;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Proof that a slice is another slice with the rows of a set set to `0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct NullifyingProof {
    /// `X̄₀ = ∗ ∖ X₀`.
    pub(crate) complement: SetHandle,
    /// `X̄₀ = ∗ ∖ X₀`.
    pub(crate) complement_proof: ComplementProof,
    /// `u[X₀] = 0`.
    pub(crate) zero_on_set: ZeroTestProof,
    /// `(u − v)[X̄₀] = 0`.
    pub(crate) equal_outside: ZeroTestProof,
}

impl NullifyingProof {
    /// Proves `u = v[X₀ → 0]` on the rows of `universe`.
    pub fn prove(
        srs: &Srs,
        universe: &Universe,
        u: &CommittedSlice,
        v: &CommittedSlice,
        x0: &CommittedSet,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let complement = universe.rows().set().difference(x0.set()).commit(srs)?;
        Self::prove_with_complement(srs, universe, u, v, x0, &complement, transcript)
    }

    /// As [`Self::prove`], with `X̄₀` already committed.
    pub(crate) fn prove_with_complement(
        srs: &Srs,
        universe: &Universe,
        u: &CommittedSlice,
        v: &CommittedSlice,
        x0: &CommittedSet,
        complement: &CommittedSet,
        transcript: &mut Transcript,
    ) -> Result<Self, Error> {
        let witness = |error| match error {
            Error::InvalidWitness(_) => Error::InvalidWitness("nullifying test"),
            error => error,
        };
        Ok(Self {
            complement: complement.handle(),
            complement_proof: ComplementProof::prove(
                srs,
                universe.rows(),
                x0,
                complement,
                transcript,
            )
            .map_err(witness)?,
            zero_on_set: ZeroTestProof::prove(srs, u, x0, transcript).map_err(witness)?,
            equal_outside: ZeroTestProof::prove(srs, &(u - v), complement, transcript)
                .map_err(witness)?,
        })
    }

    /// Verifies `u = v[X₀ → 0]` on the rows of `universe`, for the given handles.
    pub fn verify(
        &self,
        universe: UniverseHandle,
        u: SliceHandle,
        v: SliceHandle,
        x0: SetHandle,
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        self.complement_proof
            .verify(universe.rows, x0, self.complement, transcript)
            .and_then(|()| self.zero_on_set.verify(u, x0, transcript))
            .and_then(|()| {
                self.equal_outside
                    .verify(u - v, self.complement, transcript)
            })
            .map_err(|_| Error::Rejected("nullifying test"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handle::{Set, Slice};
    use ark_bls12_381::Fr;
    use ark_std::test_rng;

    // 12 rows in a domain of 16.
    const ROWS: usize = 12;

    struct Setup {
        srs: Srs,
        universe: Universe,
        v: CommittedSlice,
    }

    fn setup() -> Setup {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        let universe = Universe::new(&srs, ROWS).unwrap();
        let v = slice(&srs, |row| row as u64 + 1);
        Setup { srs, universe, v }
    }

    fn slice(srs: &Srs, value: impl Fn(usize) -> u64) -> CommittedSlice {
        Slice::new((0..ROWS).map(|row| Fr::from(value(row))).collect())
            .commit(srs)
            .unwrap()
    }

    fn set(srs: &Srs, rows: &[usize]) -> CommittedSet {
        Set::new(rows.iter().copied()).commit(srs).unwrap()
    }

    fn verify(
        proof: &NullifyingProof,
        s: &Setup,
        u: &CommittedSlice,
        x0: &CommittedSet,
    ) -> Result<(), Error> {
        let transcript = &mut Transcript::new("test");
        proof.verify(
            s.universe.handle(),
            u.handle(),
            s.v.handle(),
            x0.handle(),
            transcript,
        )
    }

    #[test]
    fn accepts_nullified_slices() {
        let s = setup();

        for rows in [vec![], vec![2, 5, 7], (0..ROWS).collect()] {
            let x0 = set(&s.srs, &rows);
            let u = slice(&s.srs, |row| {
                if rows.contains(&row) {
                    0
                } else {
                    row as u64 + 1
                }
            });
            let transcript = &mut Transcript::new("test");
            let proof =
                NullifyingProof::prove(&s.srs, &s.universe, &u, &s.v, &x0, transcript).unwrap();
            assert_eq!(verify(&proof, &s, &u, &x0), Ok(()));
        }
    }

    #[test]
    fn each_check_is_needed() {
        let s = setup();
        let x0 = set(&s.srs, &[2, 5]);
        let complement = set(&s.srs, &[0, 1, 3, 4, 6, 7, 8, 9, 10, 11]);
        let honest_u = slice(&s.srs, |row| {
            if row == 2 || row == 5 {
                0
            } else {
                row as u64 + 1
            }
        });
        let transcript = &mut Transcript::new("test");
        let honest =
            NullifyingProof::prove(&s.srs, &s.universe, &honest_u, &s.v, &x0, transcript).unwrap();
        let zero_test = |v: &CommittedSlice, set: &CommittedSet| {
            ZeroTestProof::prove(&s.srs, v, set, &mut Transcript::new("test")).unwrap()
        };
        let reject = Err(Error::Rejected("nullifying test"));

        // 1. u differs from v on row 9, left out of the claimed complement.
        let u = slice(&s.srs, |row| match row {
            2 | 5 => 0,
            9 => 100,
            _ => row as u64 + 1,
        });
        let smaller = set(&s.srs, &[0, 1, 3, 4, 6, 7, 8, 10, 11]);
        let forged = NullifyingProof {
            complement: smaller.handle(),
            zero_on_set: zero_test(&u, &x0),
            equal_outside: zero_test(&(&u - &s.v), &smaller),
            ..honest
        };
        assert_eq!(verify(&forged, &s, &u, &x0), reject);

        // 2. u is v, not zero on X₀.
        let forged = NullifyingProof {
            equal_outside: zero_test(&(&s.v - &s.v), &complement),
            ..honest
        };
        assert_eq!(verify(&forged, &s, &s.v, &x0), reject);

        // 3. u is zero on X₀ but differs from v on row 9.
        let forged = NullifyingProof {
            zero_on_set: zero_test(&u, &x0),
            ..honest
        };
        assert_eq!(verify(&forged, &s, &u, &x0), reject);
    }
}
