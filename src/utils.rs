//! This module gathers some utility functions used in the rest of the library.

use crate::{Fr, G1};
use ark_ec::VariableBaseMSM;
use ark_ff::{PrimeField, UniformRand};
use ark_poly::{univariate::DensePolynomial, Polynomial};
use ark_std::rand::{CryptoRng, Rng};

use crate::trusted_setup::SRS;

/// Commit to a polynomial, represented in dense coefficient form,
/// using a KZG10 structured reference string. Note that this is not blinding.
pub fn kzg_commit(p: &DensePolynomial<Fr>, srs: &SRS) -> G1 {
    let g1_vec = srs.elements_of_g1();
    assert!(p.degree() < g1_vec.len());

    let bigints = p.coeffs.iter().map(|c| c.into_bigint()).collect::<Vec<_>>();
    G1::msm_bigint(g1_vec, &bigints)
}

/// Generate random scalars, which can be used to blind polynomials before committing to them.
pub fn generate_blinding_scalars<R: Rng + CryptoRng>(k: usize, rng: &mut R) -> Vec<Fr> {
    (0..k).map(|_| Fr::rand(rng)).collect()
}

/// Sort a concatenated vector `(f, t)` according to `t`, and split the result
/// into elements of even index and elements of odd index.
pub fn sort_and_split(f: &Vec<Fr>, t: &Vec<Fr>) -> (Vec<Fr>, Vec<Fr>) {
    let mut sorted = [f.clone(), t.clone()].concat();
    sorted.sort_by(|a, b| {
        t.iter()
            .position(|e| e.eq(a))
            .cmp(&t.iter().position(|e| e.eq(b)))
    });
    let h1 = sorted.iter().copied().step_by(2).collect();
    let h2 = sorted.iter().copied().skip(1).step_by(2).collect();
    (h1, h2)
}
