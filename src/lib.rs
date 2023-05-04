pub mod preprocessing;
pub mod prover;
pub mod transcript;
pub mod trusted_setup;
pub mod utils;
pub mod verifier;

pub(crate) use ark_bls12_381::{Fr, G1Projective as G1, G2Projective as G2};

#[cfg(test)]
#[rustfmt::skip]
mod test {
    use super::*;
    use ark_std::{One, UniformRand, Zero, rand::SeedableRng};

    use std::collections::BTreeMap;

    #[test]
    fn prove() {
        let mut rng = rand_chacha::ChaChaRng::from_entropy();

        // ,+>[-]<.
        let v = Fr::rand(&mut rng);
        let in_table = vec![v];
        let out_table = vec![v + Fr::one()];
        let prog_text = vec![
            (Fr::zero(),     Fr::from(',' as u64), Fr::zero()    ),
            (Fr::one(),      Fr::from('+' as u64), Fr::zero()    ),
            (Fr::from(2u64), Fr::from('>' as u64), Fr::zero()    ),
            (Fr::from(3u64), Fr::from('[' as u64), Fr::from(5u64)),
            (Fr::from(4u64), Fr::from('-' as u64), Fr::zero()    ),
            (Fr::from(5u64), Fr::from(']' as u64), Fr::from(3u64)),
            (Fr::from(6u64), Fr::from('<' as u64), Fr::zero()    ),
            (Fr::from(7u64), Fr::from('.' as u64), Fr::zero()    ),
        ];
        let witness: BTreeMap<&str, Vec<Fr>> = [
            ("clk",       vec![Fr::zero(),           Fr::one(),                 Fr::from(2u64),            Fr::from(3u64),       Fr::from(4u64),       Fr::from(5u64),       Fr::from(6u64),            Fr::from(7u64)           ]),
            ("ip",        vec![Fr::zero(),           Fr::one(),                 Fr::from(2u64),            Fr::from(3u64),       Fr::from(5u64),       Fr::from(6u64),       Fr::from(7u64),            Fr::from(8u64)           ]),
            ("ci",        vec![Fr::from(',' as u64), Fr::from('+' as u64),      Fr::from('>' as u64),      Fr::from('[' as u64), Fr::from(']' as u64), Fr::from('<' as u64), Fr::from('.' as u64),      Fr::from('.' as u64)     ]),
            ("ni",        vec![Fr::zero(),           Fr::zero(),                Fr::zero(),                Fr::from(5u64),       Fr::from(3u64),       Fr::zero(),           Fr::zero(),                Fr::zero()               ]),
            ("q_fjmp",    vec![Fr::zero(),           Fr::zero(),                Fr::zero(),                Fr::one(),            Fr::zero(),           Fr::zero(),           Fr::zero(),                Fr::zero()               ]),
            ("q_bjmp",    vec![Fr::zero(),           Fr::zero(),                Fr::zero(),                Fr::zero(),           Fr::one(),            Fr::zero(),           Fr::zero(),                Fr::zero()               ]),
            ("q_right",   vec![Fr::zero(),           Fr::zero(),                Fr::one(),                 Fr::zero(),           Fr::zero(),           Fr::zero(),           Fr::zero(),                Fr::zero()               ]),
            ("q_left",    vec![Fr::zero(),           Fr::zero(),                Fr::zero(),                Fr::zero(),           Fr::zero(),           Fr::one(),            Fr::zero(),                Fr::zero()               ]),
            ("q_add",     vec![Fr::zero(),           Fr::one(),                 Fr::zero(),                Fr::zero(),           Fr::zero(),           Fr::zero(),           Fr::zero(),                Fr::zero()               ]),
            ("q_sub",     vec![Fr::zero(),           Fr::zero(),                Fr::zero(),                Fr::zero(),           Fr::zero(),           Fr::zero(),           Fr::zero(),                Fr::zero()               ]),
            ("q_in",      vec![Fr::one(),            Fr::zero(),                Fr::zero(),                Fr::zero(),           Fr::zero(),           Fr::zero(),           Fr::zero(),                Fr::zero()               ]),
            ("q_out",     vec![Fr::zero(),           Fr::zero(),                Fr::zero(),                Fr::zero(),           Fr::zero(),           Fr::zero(),           Fr::one(),                 Fr::one()                ]),
            ("mp",        vec![Fr::zero(),           Fr::zero(),                Fr::zero(),                Fr::one(),            Fr::one(),            Fr::one(),            Fr::zero(),                Fr::zero()               ]),
            ("mv",        vec![v,                    v,                         v + Fr::one(),             Fr::zero(),           Fr::zero(),           Fr::zero(),           v + Fr::one(),             v + Fr::one()            ]),
            ("inv",       vec![Fr::one()/v,          Fr::one()/v,               Fr::one()/(v + Fr::one()), Fr::zero(),           Fr::zero(),           Fr::zero(),           Fr::one()/(v + Fr::one()), Fr::one()/(v + Fr::one())]),
            ("mvz",       vec![Fr::zero(),           Fr::zero(),                Fr::zero(),                Fr::one(),            Fr::one(),            Fr::one(),            Fr::zero(),                Fr::zero()               ]),
            ("mem_mp",    vec![Fr::zero(),           Fr::zero(),                Fr::zero(),                Fr::zero(),           Fr::one(),            Fr::one(),            Fr::one(),                 Fr::one()                ]),
            ("mem_clk",   vec![Fr::zero(),           Fr::one(),                 Fr::from(2u64),            Fr::from(6u64),       Fr::from(3u64),       Fr::from(4u64),       Fr::from(5u64),            Fr::from(7u64)           ]),
            ("mem_mv",    vec![v,                    v,                         v + Fr::one(),             v + Fr::one(),        Fr::zero(),           Fr::zero(),           Fr::zero(),                Fr::zero()               ]),
            ("delta_clk", vec![Fr::one(),            Fr::one(),                 Fr::from(4u64),            Fr::zero(),           Fr::one(),            Fr::one(),            Fr::from(2u64),            Fr::zero()               ]),
        ].into();

        let srs = trusted_setup::SRS::universal_trusted_setup(&mut rng, 20);
        let preprocessed_inputs = preprocessing::PreprocessedInputs::setup(&srs, 8, in_table, out_table, prog_text);
        let proof = prover::Proof::from_computation(preprocessed_inputs.cpi(), witness, &mut rng);
        assert!(verifier::verify(&proof, &preprocessed_inputs));
    }
}
