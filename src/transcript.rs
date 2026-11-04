//! Fiat–Shamir transcript.
//!
//! Every test appends all its inputs (handles and public values) and every element of its proof
//! before drawing a challenge, so that a challenge depends on everything the verifier relies on.

use ark_bls12_381::Fr;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha512};

/// A Fiat–Shamir transcript over SHA-512.
///
/// Labels and values are length-prefixed, so different sequences of appends hash differently.
pub struct Transcript(Sha512);

impl Transcript {
    /// An empty transcript for the protocol `label`.
    pub fn new(label: &'static str) -> Self {
        let mut transcript = Self(Sha512::new());
        transcript.absorb(label.as_bytes());
        transcript
    }

    /// Appends `value`, in compressed form, under `label`.
    pub fn append<T: CanonicalSerialize + ?Sized>(&mut self, label: &'static str, value: &T) {
        let mut bytes = Vec::with_capacity(value.compressed_size());
        value
            .serialize_compressed(&mut bytes)
            .expect("serializing into a Vec does not fail");
        self.absorb(label.as_bytes());
        self.absorb(&bytes);
    }

    /// A challenge under `label`; the label is appended, so the next challenge is different.
    ///
    /// The 512-bit digest is reduced modulo the group order, with negligible bias.
    pub fn challenge(&mut self, label: &'static str) -> Fr {
        self.absorb(label.as_bytes());
        Fr::from_le_bytes_mod_order(&self.0.clone().finalize())
    }

    fn absorb(&mut self, bytes: &[u8]) {
        self.0.update((bytes.len() as u64).to_le_bytes());
        self.0.update(bytes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn challenge_after(protocol: &'static str, appends: &[(&'static str, u64)]) -> Fr {
        let mut transcript = Transcript::new(protocol);
        for (label, value) in appends {
            transcript.append(label, &Fr::from(*value));
        }
        transcript.challenge("c")
    }

    #[test]
    fn prover_and_verifier_derive_the_same_challenges() {
        let mut prover = Transcript::new("test");
        let mut verifier = Transcript::new("test");
        prover.append("x", &Fr::from(1));
        verifier.append("x", &Fr::from(1));

        let first = prover.challenge("c");
        assert_eq!(first, verifier.challenge("c"));
        // Same label again: a new challenge.
        assert_ne!(first, prover.challenge("c"));
    }

    #[test]
    fn challenge_depends_on_everything_appended() {
        let base = challenge_after("test", &[("a", 1), ("b", 2)]);

        assert_ne!(base, challenge_after("other", &[("a", 1), ("b", 2)]));
        assert_ne!(base, challenge_after("test", &[("a", 1), ("b", 3)]));
        assert_ne!(base, challenge_after("test", &[("a", 1), ("c", 2)]));
        assert_ne!(base, challenge_after("test", &[("b", 2), ("a", 1)]));
        assert_ne!(base, challenge_after("test", &[("a", 1)]));
    }
}
