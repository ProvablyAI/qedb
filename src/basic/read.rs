//! Read `data ← read(X̃, ṽ)` (Fig. 8): the values `(vⱼ)_{j ∈ X}`, from the subvector opening of
//! Fig. 4.
//!
//! The answer is the rows of `X` and their values. With `c̃` the slice equal to these values on
//! these rows and to `0` elsewhere, the prover sends `C̃ = [c̃(τ)]₁` and the verifier checks
//!
//! 1. one opening of `C̃ + γX̃` at a challenge `r` against `c̃(r) + γ·∏ⱼ (r − ωʲ)`, both computed
//!    from the answer in `O(|X|)`: `C̃` commits to the answer's values, and the answer's rows are
//!    the rows of `X̃`;
//! 2. the zero test `(ṽ − C̃)[X̃] = 0`: `v` and `c̃` agree on `X`.
//!
//! `r` and `γ` are drawn after the handles, the answer and `C̃`: with a challenge that depends on
//! `C̃` only, the prover could pick wrong values that agree with `c̃` at `r`.

use super::divide_by_linear;
use super::zero_test::ZeroTestProof;
use crate::Error;
use crate::handle::{CommittedSet, CommittedSlice, SetHandle, Slice, SliceHandle};
use crate::setup::{Domain, Srs, VerifierKey};
use crate::transcript::Transcript;
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::PrimeGroup;
use ark_ec::pairing::Pairing;
use ark_ff::{Zero, batch_inversion};
use ark_poly::EvaluationDomain;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::*;

/// Proof of the values of a slice on the rows of a set.
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReadProof {
    /// `C̃ = [c̃(τ)]₁`.
    pub(crate) sparse: SliceHandle,
    /// The opening of `C̃ + γX̃` at `r`.
    pub(crate) opening: G1Projective,
    /// `(ṽ − C̃)[X̃] = 0`.
    pub(crate) zero_test: ZeroTestProof,
}

impl ReadProof {
    /// Reads the values of `v` on the rows of `X`, in increasing row order, with their proof.
    pub fn prove(
        srs: &Srs,
        v: &CommittedSlice,
        x: &CommittedSet,
        transcript: &mut Transcript,
    ) -> Result<(Vec<Fr>, Self), Error> {
        let all = v.slice().values();
        let rows = x.set().rows();
        let values: Vec<Fr> = rows
            .iter()
            .map(|&row| all.get(row).copied().unwrap_or_default())
            .collect();

        let (sparse, opening) = open_sparse(srs, v.handle(), x, rows, &values, transcript)?;
        let zero_test = ZeroTestProof::prove(srs, &(v - &sparse), x, transcript)?;
        let proof = Self {
            sparse: sparse.handle(),
            opening,
            zero_test,
        };
        Ok((values, proof))
    }

    /// Verifies that `values` are the values of the slice `ṽ` on `rows`, the rows of the set `X̃`
    /// in increasing order.
    pub fn verify(
        &self,
        vk: &VerifierKey,
        v: SliceHandle,
        x: SetHandle,
        rows: &[usize],
        values: &[Fr],
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        let domain = vk.domain();
        if rows.len() != values.len()
            || !rows.windows(2).all(|pair| pair[0] < pair[1])
            || rows.last().is_some_and(|&row| row >= domain.size())
        {
            return Err(Error::Rejected("read"));
        }

        let (r, gamma) = challenges(v, x, rows, values, self.sparse, transcript);
        let (sparse_at_r, set_at_r) = evaluate_answer(domain, rows, values, r);
        let y = sparse_at_r + gamma * set_at_r;
        // e(C̃ + γX̃ − y[1]₁, [1]₂) = e(π, [τ − r]₂)
        let g1 = G1Projective::generator();
        let check = Bls12_381::multi_pairing(
            [
                self.sparse.0 + x.0 * gamma - g1 * y + self.opening * r,
                -self.opening,
            ],
            [G2Projective::generator(), G2Projective::from(vk.tau)],
        );
        if !check.is_zero() {
            return Err(Error::Rejected("read"));
        }

        transcript.append("read: opening", &self.opening);
        self.zero_test
            .verify(v - self.sparse, x, transcript)
            .map_err(|_| Error::Rejected("read"))
    }
}

/// Commits to the slice `c̃` with `values` on `rows` (rows of the domain), and opens `c̃ + γ·P_X`
/// at the challenge `r`.
fn open_sparse(
    srs: &Srs,
    v: SliceHandle,
    x: &CommittedSet,
    rows: &[usize],
    values: &[Fr],
    transcript: &mut Transcript,
) -> Result<(CommittedSlice, G1Projective), Error> {
    let mut sparse = vec![Fr::zero(); srs.domain().size()];
    for (&row, &value) in rows.iter().zip(values) {
        sparse[row] = value;
    }
    let sparse = Slice::new(sparse).commit(srs)?;

    let (r, gamma) = challenges(v, x.handle(), rows, values, sparse.handle(), transcript);
    let p = sparse.polynomial() + &(x.polynomial() * gamma);
    let opening = srs.commit_g1(&divide_by_linear(&p, r))?;
    transcript.append("read: opening", &opening);
    Ok((sparse, opening))
}

fn challenges(
    v: SliceHandle,
    x: SetHandle,
    rows: &[usize],
    values: &[Fr],
    sparse: SliceHandle,
    transcript: &mut Transcript,
) -> (Fr, Fr) {
    transcript.append("read: slice", &v);
    transcript.append("read: set", &x);
    transcript.append("read: rows", rows);
    transcript.append("read: values", values);
    transcript.append("read: sparse slice", &sparse);
    (
        transcript.challenge("read: r"),
        transcript.challenge("read: gamma"),
    )
}

/// `c̃(r) = Σⱼ vⱼ·λⱼ(r)` and `∏ⱼ (r − ωʲ)` over the answer's rows `j`, in `O(|X|)`, with
/// `λⱼ(r) = ωʲ·(rᴺ − 1) / (N·(r − ωʲ))`.
fn evaluate_answer(domain: &Domain, rows: &[usize], values: &[Fr], r: Fr) -> (Fr, Fr) {
    let points: Vec<Fr> = rows.par_iter().map(|&row| domain.element(row)).collect();
    let mut denominators: Vec<Fr> = points.par_iter().map(|w| r - w).collect();
    let set_at_r: Fr = denominators.par_iter().product();
    if set_at_r.is_zero() {
        // r is the point of one of the rows.
        let value = points.iter().zip(values).find(|(w, _)| **w == r);
        return (value.map(|(_, v)| *v).unwrap_or_default(), set_at_r);
    }

    batch_inversion(&mut denominators);
    let sum: Fr = points
        .par_iter()
        .zip(&denominators)
        .zip(values)
        .map(|((w, d), v)| *v * w * d)
        .sum();
    let sparse_at_r = sum * domain.evaluate_vanishing_polynomial(r) * domain.size_inv;
    (sparse_at_r, set_at_r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handle::Set;
    use ark_ff::Field;
    use ark_std::test_rng;

    fn setup() -> (Srs, CommittedSlice) {
        let srs = Srs::setup(16, &mut test_rng()).unwrap();
        // 12 values on 16 rows: rows 12.. are 0.
        let v = Slice::new((1..=12).map(Fr::from).collect())
            .commit(&srs)
            .unwrap();
        (srs, v)
    }

    fn set(srs: &Srs, rows: &[usize]) -> CommittedSet {
        Set::new(rows.iter().copied()).commit(srs).unwrap()
    }

    fn prove(srs: &Srs, v: &CommittedSlice, x: &CommittedSet) -> (Vec<Fr>, ReadProof) {
        ReadProof::prove(srs, v, x, &mut Transcript::new("test")).unwrap()
    }

    fn verify(
        proof: &ReadProof,
        srs: &Srs,
        v: &CommittedSlice,
        x: &CommittedSet,
        rows: &[usize],
        values: &[Fr],
    ) -> Result<(), Error> {
        let transcript = &mut Transcript::new("test");
        proof.verify(
            &srs.verifier_key(),
            v.handle(),
            x.handle(),
            rows,
            values,
            transcript,
        )
    }

    #[test]
    fn reads_the_values_on_the_set() {
        let (srs, v) = setup();

        for rows in [vec![], vec![1, 4, 7, 12], (0..16).collect()] {
            let x = set(&srs, &rows);
            let (values, proof) = prove(&srs, &v, &x);
            let expected: Vec<Fr> = rows
                .iter()
                .map(|&row| Fr::from(if row < 12 { row as u64 + 1 } else { 0 }))
                .collect();
            assert_eq!(values, expected);
            assert_eq!(verify(&proof, &srs, &v, &x, &rows, &values), Ok(()));
        }
    }

    #[test]
    fn rejects_a_wrong_value() {
        let (srs, v) = setup();
        let rows = [1, 4, 7];
        let x = set(&srs, &rows);
        let (mut values, honest) = prove(&srs, &v, &x);
        values[1] += Fr::ONE;
        assert_eq!(
            verify(&honest, &srs, &v, &x, &rows, &values),
            Err(Error::Rejected("read"))
        );

        // C̃ commits to the wrong value and opens correctly: only the zero test catches it.
        let transcript = &mut Transcript::new("test");
        let (sparse, opening) =
            open_sparse(&srs, v.handle(), &x, &rows, &values, transcript).unwrap();
        let forged = ReadProof {
            sparse: sparse.handle(),
            opening,
            zero_test: honest.zero_test,
        };
        assert_eq!(
            verify(&forged, &srs, &v, &x, &rows, &values),
            Err(Error::Rejected("read"))
        );
    }

    #[test]
    fn rejects_a_row_outside_the_set() {
        let (srs, v) = setup();
        let x = set(&srs, &[1, 4]);
        // A made-up value on row 9 ∉ X. The zero test only covers X: only the opening of X̃
        // catches it.
        let (rows, values) = ([1, 4, 9], [Fr::from(2), Fr::from(5), Fr::from(100)]);
        let transcript = &mut Transcript::new("test");
        let (sparse, opening) =
            open_sparse(&srs, v.handle(), &x, &rows, &values, transcript).unwrap();
        let zero_test = ZeroTestProof::prove(&srs, &(&v - &sparse), &x, transcript).unwrap();
        let forged = ReadProof {
            sparse: sparse.handle(),
            opening,
            zero_test,
        };

        assert_eq!(
            verify(&forged, &srs, &v, &x, &rows, &values),
            Err(Error::Rejected("read"))
        );
    }

    #[test]
    fn rejects_values_that_agree_with_the_sparse_slice_at_r() {
        let (srs, v) = setup();
        let rows = [1, 4, 7];
        let x = set(&srs, &rows);
        let (values, proof) = prove(&srs, &v, &x);
        // The r of the honest proof. Changing rows 1 and 4 by λ₄(r) and −λ₁(r) leaves c̃(r)
        // unchanged: accepted if r did not depend on the values.
        let transcript = &mut Transcript::new("test");
        let (r, _) = challenges(
            v.handle(),
            x.handle(),
            &rows,
            &values,
            proof.sparse,
            transcript,
        );
        let lambda = |row| evaluate_answer(srs.domain(), &[row], &[Fr::ONE], r).0;
        let mut wrong = values;
        wrong[0] += lambda(4);
        wrong[1] -= lambda(1);

        assert_eq!(
            verify(&proof, &srs, &v, &x, &rows, &wrong),
            Err(Error::Rejected("read"))
        );
    }
}
