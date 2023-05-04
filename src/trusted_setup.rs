use crate::{Fr, G1, G2};
use ark_bls12_381::G1Affine;
use ark_ec::{CurveGroup, Group};
use ark_ff::{Field, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{CryptoRng, Rng};

/// A KZG10 structured reference string.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SRS {
    elements_of_g1: Vec<G1Affine>,
    elements_of_g2: [G2; 2],
}

impl SRS {
    /// Randomly generate a `SRS` of size `n`.
    pub fn universal_trusted_setup<R: Rng + CryptoRng>(rng: &mut R, n: usize) -> Self {
        let x = Fr::rand(rng);
        let elements_of_g1 = (0..n)
            .map(|i| (G1::generator() * x.pow([i as u64])).into_affine())
            .collect();
        let elements_of_g2 = [G2::generator(), G2::generator() * x];
        Self {
            elements_of_g1,
            elements_of_g2,
        }
    }

    /// Trim a `SRS` to size `size`.
    pub fn trim(&self, size: usize) -> Self {
        Self {
            elements_of_g1: self.elements_of_g1.iter().copied().take(size).collect(),
            elements_of_g2: self.elements_of_g2.clone(),
        }
    }

    pub fn elements_of_g1(&self) -> &[G1Affine] {
        &self.elements_of_g1
    }

    pub fn elements_of_g2(&self) -> &[G2; 2] {
        &self.elements_of_g2
    }
}
