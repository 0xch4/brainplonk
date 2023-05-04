use ark_poly::{EvaluationDomain, Evaluations, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{One, Zero};

use crate::trusted_setup::SRS;
use crate::utils::kzg_commit;
use crate::{Fr, G1};

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommonPreprocessedInputs {
    pub(crate) n: usize,
    pub(crate) domain: Radix2EvaluationDomain<Fr>,
    pub(crate) srs: SRS,
    pub(crate) prog_text: Vec<(Fr, Fr, Fr)>,
    pub(crate) in_table: Vec<Fr>,
    pub(crate) out_table: Vec<Fr>,
}

#[derive(Clone, Debug)]
pub struct VerifierPreprocessedInputs {
    pub(crate) com_prog_text: (G1, G1, G1),
    pub(crate) com_opc_table: (G1, [G1; 8]),
    pub(crate) com_clk_table: G1,
}

#[derive(Clone, Debug)]
pub struct PreprocessedInputs {
    cpi: CommonPreprocessedInputs,
    vpi: VerifierPreprocessedInputs,
}

impl PreprocessedInputs {
    /// Generate appropriate preprocessed inputs from a universal structured reference string `srs`,
    /// trace size `n`, program text `prog_text`, and input and output tables `in_table` and `out_table`.
    pub fn setup(
        srs: &SRS,
        n: usize,
        in_table: Vec<Fr>,
        out_table: Vec<Fr>,
        prog_text: Vec<(Fr, Fr, Fr)>,
    ) -> Self {
        assert!(prog_text.len() <= n);
        assert!(out_table.len() <= n);
        assert!(in_table.len() <= n);
        assert!(n.is_power_of_two());
        assert!(n >= 8);

        let domain = Radix2EvaluationDomain::new(n).unwrap();

        let unzipped_prog_text: (Vec<Fr>, (Vec<Fr>, Vec<Fr>)) =
            prog_text.iter().map(|(ip, ci, ni)| (ip, (ci, ni))).unzip();
        let com_prog_text = (
            kzg_commit(
                &Evaluations::from_vec_and_domain(unzipped_prog_text.0, domain).interpolate(),
                srs,
            ),
            kzg_commit(
                &Evaluations::from_vec_and_domain(unzipped_prog_text.1 .0, domain).interpolate(),
                srs,
            ),
            kzg_commit(
                &Evaluations::from_vec_and_domain(unzipped_prog_text.1 .1, domain).interpolate(),
                srs,
            ),
        );

        let com_opc_table = (
            kzg_commit(
                &Evaluations::from_vec_and_domain(
                    [
                        vec![
                            Fr::from('[' as u64),
                            Fr::from(']' as u64),
                            Fr::from('+' as u64),
                            Fr::from('-' as u64),
                            Fr::from('<' as u64),
                            Fr::from('>' as u64),
                            Fr::from(',' as u64),
                            Fr::from('.' as u64),
                        ],
                        vec![Fr::from('.' as u64); n - 8],
                    ]
                    .concat(),
                    domain,
                )
                .interpolate(),
                srs,
            ),
            [
                kzg_commit(
                    &Evaluations::from_vec_and_domain(
                        [vec![Fr::one()], vec![Fr::zero(); n - 1]].concat(),
                        domain,
                    )
                    .interpolate(),
                    srs,
                ),
                kzg_commit(
                    &Evaluations::from_vec_and_domain(
                        [vec![Fr::zero(), Fr::one()], vec![Fr::zero(); n - 2]].concat(),
                        domain,
                    )
                    .interpolate(),
                    srs,
                ),
                kzg_commit(
                    &Evaluations::from_vec_and_domain(
                        [
                            vec![Fr::zero(), Fr::zero(), Fr::one()],
                            vec![Fr::zero(); n - 3],
                        ]
                        .concat(),
                        domain,
                    )
                    .interpolate(),
                    srs,
                ),
                kzg_commit(
                    &Evaluations::from_vec_and_domain(
                        [
                            vec![Fr::zero(), Fr::zero(), Fr::zero(), Fr::one()],
                            vec![Fr::zero(); n - 4],
                        ]
                        .concat(),
                        domain,
                    )
                    .interpolate(),
                    srs,
                ),
                kzg_commit(
                    &Evaluations::from_vec_and_domain(
                        [
                            vec![Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::one()],
                            vec![Fr::zero(); n - 5],
                        ]
                        .concat(),
                        domain,
                    )
                    .interpolate(),
                    srs,
                ),
                kzg_commit(
                    &Evaluations::from_vec_and_domain(
                        [
                            vec![
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::one(),
                            ],
                            vec![Fr::zero(); n - 6],
                        ]
                        .concat(),
                        domain,
                    )
                    .interpolate(),
                    srs,
                ),
                kzg_commit(
                    &Evaluations::from_vec_and_domain(
                        [
                            vec![
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::one(),
                            ],
                            vec![Fr::zero(); n - 7],
                        ]
                        .concat(),
                        domain,
                    )
                    .interpolate(),
                    srs,
                ),
                kzg_commit(
                    &Evaluations::from_vec_and_domain(
                        [
                            vec![
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::zero(),
                                Fr::one(),
                            ],
                            vec![Fr::zero(); n - 8],
                        ]
                        .concat(),
                        domain,
                    )
                    .interpolate(),
                    srs,
                ),
            ],
        );
        let com_clk_table = kzg_commit(
            &Evaluations::from_vec_and_domain(
                (1..=n).map(|i| Fr::from(i as u64)).collect(),
                domain,
            )
            .interpolate(),
            srs,
        );

        Self {
            cpi: CommonPreprocessedInputs {
                n,
                domain,
                srs: srs.trim(n + 6),
                prog_text,
                in_table,
                out_table,
            },
            vpi: VerifierPreprocessedInputs {
                com_prog_text,
                com_opc_table,
                com_clk_table,
            },
        }
    }

    pub fn cpi(&self) -> &CommonPreprocessedInputs {
        &self.cpi
    }

    pub fn vpi(&self) -> &VerifierPreprocessedInputs {
        &self.vpi
    }
}
