use crate::preprocessing::CommonPreprocessedInputs;
use crate::{Fr, G1};
use ark_ff::{Field, PrimeField};
use ark_serialize::CanonicalSerialize;
use merlin::Transcript;

/// The trait that defines the operations needed for a transcript to be used in BrainPlonk.
pub(crate) trait TranscriptProtocol {
    fn init(&mut self, inputs: &CommonPreprocessedInputs);
    fn append_commitments(&mut self, label: &'static [u8], commitments: &[G1]);
    fn append_evaluations(&mut self, label: &'static [u8], evaluations: &[Fr]);
    fn challenge_scalars(&mut self, k: usize) -> Vec<Fr>;
}

impl TranscriptProtocol for Transcript {
    fn init(&mut self, inputs: &CommonPreprocessedInputs) {
        let mut compressed_bytes = Vec::new();
        inputs.serialize_compressed(&mut compressed_bytes).unwrap();

        self.append_message(b"common preprocessed inputs", &compressed_bytes);
    }

    fn append_commitments(&mut self, label: &'static [u8], commitments: &[G1]) {
        for commitment in commitments {
            let mut compressed_bytes = Vec::new();
            commitment
                .serialize_compressed(&mut compressed_bytes)
                .unwrap();
            self.append_message(label, &compressed_bytes);
        }
    }

    fn append_evaluations(&mut self, label: &'static [u8], evaluations: &[Fr]) {
        for evaluation in evaluations {
            let mut compressed_bytes = Vec::new();
            evaluation
                .serialize_compressed(&mut compressed_bytes)
                .unwrap();
            self.append_message(label, &compressed_bytes);
        }
    }

    fn challenge_scalars(&mut self, k: usize) -> Vec<Fr> {
        assert!(k > 0);
        let chunk_size = Fr::MODULUS_BIT_SIZE as usize / 8;
        let mut bytes = vec![0u8; k * chunk_size];
        self.challenge_bytes(b"", &mut bytes);
        bytes
            .chunks(chunk_size)
            .map(|b| Fr::from_random_bytes(b).unwrap())
            .collect()
    }
}
