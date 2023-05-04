use std::{
    collections::BTreeMap,
    ops::{Add, Div, Mul, Sub},
};

use ark_bls12_381::{Fr, G1Projective as G1};
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial,
    Radix2EvaluationDomain,
};
use ark_std::{
    rand::{CryptoRng, Rng},
    One, Zero,
};
use merlin::Transcript;

use crate::{
    preprocessing::CommonPreprocessedInputs,
    transcript::TranscriptProtocol,
    utils::{generate_blinding_scalars, kzg_commit, sort_and_split},
};

/// A collection of commitments to polynomials, included in a proof.
#[derive(Clone, Debug)]
pub struct Commitments {
    witness: BTreeMap<String, G1>,
    fh1h2: BTreeMap<String, [G1; 3]>,
    z: BTreeMap<String, G1>,
    q: BTreeMap<String, G1>,
    w: BTreeMap<String, G1>,
}

impl Commitments {
    fn new() -> Self {
        Self {
            witness: BTreeMap::new(),
            fh1h2: BTreeMap::new(),
            z: BTreeMap::new(),
            q: BTreeMap::new(),
            w: BTreeMap::new(),
        }
    }

    /// Validate that all commitments are on the curve and in the correct subgroup.
    pub fn validate(&self) -> bool {
        for (_, c) in self
            .witness()
            .iter()
            .chain(self.z.iter())
            .chain(self.q.iter())
            .chain(self.w.iter())
        {
            let aff_c = c.into_affine();
            if !aff_c.is_on_curve() || !aff_c.is_in_correct_subgroup_assuming_on_curve() {
                return false;
            }
        }

        for (_, [c1, c2, c3]) in self.fh1h2().iter() {
            let aff_c1 = c1.into_affine();
            let aff_c2 = c2.into_affine();
            let aff_c3 = c3.into_affine();
            if !aff_c1.is_on_curve() || !aff_c1.is_in_correct_subgroup_assuming_on_curve() {
                return false;
            }
            if !aff_c2.is_on_curve() || !aff_c2.is_in_correct_subgroup_assuming_on_curve() {
                return false;
            }
            if !aff_c3.is_on_curve() || !aff_c3.is_in_correct_subgroup_assuming_on_curve() {
                return false;
            }
        }

        true
    }

    pub fn witness(&self) -> &BTreeMap<String, G1> {
        &self.witness
    }

    pub fn fh1h2(&self) -> &BTreeMap<String, [G1; 3]> {
        &self.fh1h2
    }

    pub fn z(&self) -> &BTreeMap<String, G1> {
        &self.z
    }

    pub fn q(&self) -> &BTreeMap<String, G1> {
        &self.q
    }

    pub fn w(&self) -> &BTreeMap<String, G1> {
        &self.w
    }
}

/// A collection of polynomial opening evaluations, used in a proof.
#[derive(Clone, Debug)]
pub struct Openings {
    witness: BTreeMap<String, Fr>,
    ttfh1h2: BTreeMap<String, [Fr; 5]>,
    z: BTreeMap<String, Fr>,
}

impl Openings {
    fn new() -> Self {
        Self {
            witness: BTreeMap::new(),
            ttfh1h2: BTreeMap::new(),
            z: BTreeMap::new(),
        }
    }

    pub fn witness(&self) -> &BTreeMap<String, Fr> {
        &self.witness
    }

    pub fn ttfh1h2(&self) -> &BTreeMap<String, [Fr; 5]> {
        &self.ttfh1h2
    }

    pub fn z(&self) -> &BTreeMap<String, Fr> {
        &self.z
    }
}

/// A Plonkish proof, gathering both polynomial commitments and opening evaluations.
#[derive(Clone, Debug)]
pub struct Proof {
    commitments: Commitments,
    opening_evaluations: Openings,
}

impl Proof {
    pub fn commitments(&self) -> &Commitments {
        &self.commitments
    }

    pub fn opening_evaluations(&self) -> &Openings {
        &self.opening_evaluations
    }

    /// Generate a zero-knowledge proof for the given witness to a computation.
    pub fn from_computation<R: Rng + CryptoRng>(
        cpi: &CommonPreprocessedInputs,
        witness: BTreeMap<&str, Vec<Fr>>,
        rng: &mut R,
    ) -> Self {
        let mut commitments = Commitments::new();
        let mut opening_evaluations = Openings::new();
        let mut transcript = Transcript::new(b"BrainPlonk");
        transcript.init(cpi);

        let n = cpi.n;
        let domain = cpi.domain;
        let omega = domain.group_gen;
        let extended_domain = Radix2EvaluationDomain::<Fr>::new(8 * n).unwrap();
        let zh = domain
            .vanishing_polynomial()
            .evaluate_over_domain(extended_domain);
        let one = Evaluations::from_vec_and_domain(vec![Fr::one(); 8 * n], extended_domain);
        let x =
            Evaluations::from_vec_and_domain(extended_domain.elements().collect(), extended_domain);
        let x2 = Evaluations::from_vec_and_domain(
            extended_domain
                .elements()
                .map(|e| e.pow([2 as u64]))
                .collect(),
            extended_domain,
        );

        let low_degree_extension = |values: Vec<Fr>| {
            let evals = Evaluations::from_vec_and_domain(values, domain);
            let extended = evals
                .interpolate_by_ref()
                .evaluate_over_domain(extended_domain);
            (evals.evals, extended)
        };

        let shift = |p: &DensePolynomial<Fr>| {
            let mut p = p.clone();
            let mut factor = Fr::one();
            p.coeffs.iter_mut().for_each(|c| {
                *c *= &factor;
                factor *= &omega;
            });
            p.evaluate_over_domain(extended_domain)
        };

        //
        // Round 1
        //
        let b = generate_blinding_scalars::<R>(40, rng);

        let (witness, (w, p_w)): (
            BTreeMap<&str, Vec<Fr>>,
            (
                BTreeMap<&str, Evaluations<Fr, Radix2EvaluationDomain<Fr>>>,
                BTreeMap<&str, DensePolynomial<Fr>>,
            ),
        ) = witness
            .into_iter()
            .enumerate()
            .map(|(i, (k, v))| {
                let (w, mut lde_w) = low_degree_extension(v);
                lde_w = lde_w.add(&zh.mul(&x.mul(b[2 * i]).add(&one.mul(b[2 * i + 1]))));
                let p_w = lde_w.interpolate_by_ref();
                let com_w = kzg_commit(&p_w, &cpi.srs);
                transcript.append_commitments(b"round1", &[com_w]);
                commitments.witness.insert(k.to_string(), com_w);
                ((k, w), ((k, lde_w), (k, p_w)))
            })
            .unzip();

        //
        // Round 2
        //  There are three lookup arguments that we need to compute:
        //      - all executed instructions pertain to the program text (txt)
        //      - delta_clk, when non-zero, is in [1, n] (clk)
        //      - the pseudo-selectors q_* are computed corretly from the opcode ci (opc)
        //
        let zeta = transcript.challenge_scalars(2);
        let b = generate_blinding_scalars::<R>(21, rng);

        let last_ip = cpi.prog_text.iter().max_by_key(|(ip, _, _)| ip).unwrap();
        let f_txt = witness["ip"]
            .iter()
            .zip(witness["ci"].iter())
            .zip(witness["ni"].iter())
            .map(|((&ip, &ci), &ni)| {
                if ip > last_ip.0 {
                    last_ip.0 + zeta[0] * last_ip.1 + zeta[0].pow([2 as u64]) * last_ip.2
                } else {
                    ip + zeta[0] * ci + zeta[0].pow([2 as u64]) * ni
                }
            })
            .collect::<Vec<_>>();
        let t_txt = [
            cpi.prog_text
                .iter()
                .map(|&(ip, ci, ni)| ip + zeta[0] * ci + zeta[0].pow([2 as u64]) * ni)
                .collect::<Vec<_>>(),
            vec![
                last_ip.0 + zeta[0] * last_ip.1 + zeta[0].pow([2 as u64]) * last_ip.2;
                n - cpi.prog_text.len()
            ],
        ]
        .concat();

        let f_clk = witness["delta_clk"]
            .iter()
            .map(|&delta_clk| {
                if delta_clk.is_zero() {
                    Fr::from(n as u64)
                } else {
                    delta_clk
                }
            })
            .collect();
        let t_clk: Vec<Fr> = (1..=n).map(|i| Fr::from(i as u64)).collect();

        let f_opc = witness["ci"]
            .iter()
            .zip(witness["q_fjmp"].iter())
            .zip(witness["q_bjmp"].iter())
            .zip(witness["q_add"].iter())
            .zip(witness["q_sub"].iter())
            .zip(witness["q_left"].iter())
            .zip(witness["q_right"].iter())
            .zip(witness["q_in"].iter())
            .zip(witness["q_out"].iter())
            .map(
                |(
                    (((((((&ci, &q_fjmp), &q_bjmp), &q_add), &q_sub), &q_left), &q_right), &q_in),
                    &q_out,
                )| {
                    ci + zeta[1] * q_fjmp
                        + zeta[1].pow([2 as u64]) * q_bjmp
                        + zeta[1].pow([3 as u64]) * q_add
                        + zeta[1].pow([4 as u64]) * q_sub
                        + zeta[1].pow([5 as u64]) * q_left
                        + zeta[1].pow([6 as u64]) * q_right
                        + zeta[1].pow([7 as u64]) * q_in
                        + zeta[1].pow([8 as u64]) * q_out
                },
            )
            .collect::<Vec<_>>();
        let t_opc = [
            vec![
                Fr::from('[' as u64) + zeta[1].pow([1 as u64]),
                Fr::from(']' as u64) + zeta[1].pow([2 as u64]),
                Fr::from('+' as u64) + zeta[1].pow([3 as u64]),
                Fr::from('-' as u64) + zeta[1].pow([4 as u64]),
                Fr::from('<' as u64) + zeta[1].pow([5 as u64]),
                Fr::from('>' as u64) + zeta[1].pow([6 as u64]),
                Fr::from(',' as u64) + zeta[1].pow([7 as u64]),
                Fr::from('.' as u64) + zeta[1].pow([8 as u64]),
            ],
            vec![Fr::from('.' as u64) + zeta[1].pow([8 as u64]); n - 8],
        ]
        .concat();

        let tfh1h2 = [
            ("txt", f_txt, t_txt),
            ("clk", f_clk, t_clk),
            ("opc", f_opc, t_opc),
        ]
        .into_iter()
        .enumerate()
        .map(|(i, (k, f, t))| {
            let j = i * 7;
            let (f, mut lde_f) = low_degree_extension(f);
            lde_f = lde_f.add(&zh.mul(&x.mul(b[j]).add(&one.mul(b[j + 1]))));
            let p_f = lde_f.interpolate_by_ref();
            let (h1, h2) = sort_and_split(&f, &t);
            let (h1, mut lde_h1) = low_degree_extension(h1);
            let (h2, mut lde_h2) = low_degree_extension(h2);
            lde_h1 = lde_h1.add(
                &zh.mul(
                    &x2.mul(b[j + 2])
                        .add(&x.mul(b[j + 3]).add(&one.mul(b[j + 4]))),
                ),
            );
            let p_h1 = lde_h1.interpolate_by_ref();
            lde_h2 = lde_h2.add(&zh.mul(&(x.mul(b[j + 5]).add(&one.mul(b[j + 6])))));
            let p_h2 = lde_h2.interpolate_by_ref();
            let com_f = kzg_commit(&p_f, &cpi.srs);
            let com_h1 = kzg_commit(&p_h1, &cpi.srs);
            let com_h2 = kzg_commit(&p_h2, &cpi.srs);
            commitments
                .fh1h2
                .insert(k.to_string(), [com_f, com_h1, com_h2]);
            let (t, lde_t) = low_degree_extension(t);
            let p_t = lde_t.interpolate_by_ref();
            (
                k,
                (
                    (t, lde_t, p_t),
                    (f, lde_f, p_f),
                    (h1, lde_h1, p_h1),
                    (h2, lde_h2, p_h2),
                ),
            )
        })
        .collect::<BTreeMap<&str, _>>();
        commitments
            .fh1h2
            .values()
            .for_each(|coms| transcript.append_commitments(b"round2", coms));

        //
        // Round 3
        //  In addition to the 'z' polynomials for the lookup arguments, we also have
        //  the polynomial for the memory permutation argument (mem), and the polynomials for
        //  the IO correctness arguments (in and out).
        //
        let xi = transcript.challenge_scalars(10);
        let b = generate_blinding_scalars::<R>(18, rng);

        let mut z_mem = vec![Fr::one(); n];
        let beta = xi[0];
        let gamma = xi[1];
        for i in 0..n - 1 {
            z_mem[i + 1] = z_mem[i]
                * (witness["mp"][i]
                    + beta * witness["clk"][i]
                    + beta.pow([2 as u64]) * witness["mv"][i]
                    + gamma)
                / (witness["mem_mp"][i]
                    + beta * witness["mem_clk"][i]
                    + beta.pow([2 as u64]) * witness["mem_mv"][i]
                    + gamma);
        }

        let (z_plookups, (delta, epsilon)): (Vec<_>, (BTreeMap<&str, _>, BTreeMap<&str, _>)) =
            tfh1h2
                .iter()
                .enumerate()
                .map(
                    |(j, (&k, ((t, _, _), (f, _, _), (h1, _, _), (h2, _, _))))| {
                        let mut z = vec![Fr::one(); n];
                        let delta = xi[2 * j + 2];
                        let epsilon = xi[2 * j + 3];
                        for i in 0..n - 1 {
                            z[i + 1] = z[i]
                                * ((Fr::one() + delta)
                                    * (epsilon + f[i])
                                    * (epsilon * (Fr::one() + delta) + t[i] + delta * t[i + 1]))
                                / ((epsilon * (Fr::one() + delta) + h1[i] + delta * h2[i])
                                    * (epsilon * (Fr::one() + delta) + h2[i] + delta * h1[i + 1]));
                        }
                        ((k, z), ((k, delta), (k, epsilon)))
                    },
                )
                .unzip();

        let mut z_in = vec![Fr::zero(); n];
        let mut z_out = vec![Fr::zero(); n];
        for i in 1..n {
            z_in[i] = if witness["q_in"][i - 1] == Fr::one() {
                witness["mv"][i - 1] + xi[8] * z_in[i - 1]
            } else {
                z_in[i - 1]
            };

            z_out[i] = if witness["q_out"][i - 1] == Fr::one() {
                witness["mv"][i - 1] + xi[9] * z_out[i - 1]
            } else {
                z_out[i - 1]
            };
        }
        let terminal_in = cpi
            .in_table
            .iter()
            .fold(Fr::zero(), |acc, &v| v + xi[8] * acc);
        let terminal_out = cpi
            .out_table
            .iter()
            .fold(Fr::zero(), |acc, &v| v + xi[9] * acc);
        assert_eq!(z_in[n - 1], terminal_in);
        assert_eq!(z_out[n - 1], terminal_out);

        let z = z_plookups
            .into_iter()
            .chain([("mem", z_mem), ("in", z_in), ("out", z_out)].into_iter())
            .enumerate()
            .map(|(i, (k, z))| {
                let j = i * 2;
                let (z, mut lde_z) = low_degree_extension(z);
                lde_z =
                    lde_z.add(&zh.mul(&x2.mul(b[j]).add(&x.mul(b[j + 1]).add(&one.mul(b[j + 2])))));
                let p_z = lde_z.interpolate_by_ref();
                let com_z = kzg_commit(&p_z, &cpi.srs);
                commitments.z.insert(k.to_string(), com_z);
                (k, (z, lde_z, p_z))
            })
            .collect::<BTreeMap<&str, _>>();
        transcript.append_commitments(
            b"round3",
            &commitments.z.values().copied().collect::<Vec<_>>(),
        );

        //
        // Round 4
        //
        let alpha = transcript.challenge_scalars(1)[0];
        let b = generate_blinding_scalars::<R>(4, rng);
        let (_, l1) = low_degree_extension([vec![Fr::one()], vec![Fr::zero(); n - 1]].concat());
        let (_, ln) = low_degree_extension([vec![Fr::zero(); n - 1], vec![Fr::one()]].concat());

        let constraints = vec![
            // z_out is computed correctly and takes expected extremal values
            (&one.sub(&ln)).mul(
                &shift(&z["out"].2).sub(
                    &w["q_out"]
                        .mul(&z["out"].1.mul(xi[9]).add(&w["mv"]))
                        .add(&(one.sub(&w["q_out"])).mul(&z["out"].1)),
                ),
            ),
            z["out"].1.mul(&l1),
            z["out"].1.sub(&one.mul(terminal_out)).mul(&ln),
            // z_in is computed correctly and takes expected extremal values
            (&one.sub(&ln)).mul(
                &shift(&z["in"].2).sub(
                    &w["q_in"]
                        .mul(&z["in"].1.mul(xi[8]).add(&w["mv"]))
                        .add(&(one.sub(&w["q_in"])).mul(&z["in"].1)),
                ),
            ),
            z["in"].1.mul(&l1),
            z["in"].1.sub(&one.mul(terminal_in)).mul(&ln),
            // z_mem is computed correctly and takes expected extremal values
            (&one.sub(&ln)).mul(
                &shift(&z["mem"].2)
                    .mul(
                        &w["mem_mp"]
                            .add(&w["mem_clk"].mul(beta))
                            .add(&w["mem_mv"].mul(beta.pow([2 as u64])))
                            .add(&one.mul(gamma)),
                    )
                    .sub(
                        &z["mem"].1.mul(
                            &w["mp"]
                                .add(&w["clk"].mul(beta))
                                .add(&w["mv"].mul(beta.pow([2 as u64])))
                                .add(&one.mul(gamma)),
                        ),
                    ),
            ),
            z["mem"].1.sub(&one).mul(&l1),
            z["mem"].1.sub(&one).mul(&ln),
            // z_txt is computed from correct f_txt and takes expected extremal values
            (&one.sub(&ln)).mul(
                &(shift(&z["txt"].2)
                    .mul(
                        &one.add(&one.mul(delta["txt"]))
                            .mul(epsilon["txt"])
                            .add(&tfh1h2["txt"].2 .1)
                            .add(&tfh1h2["txt"].3 .1.mul(delta["txt"])),
                    )
                    .mul(
                        &one.add(&one.mul(delta["txt"]))
                            .mul(epsilon["txt"])
                            .add(&tfh1h2["txt"].3 .1)
                            .add(&shift(&tfh1h2["txt"].2 .2).mul(delta["txt"])),
                    ))
                .sub(
                    &(z["txt"].1)
                        .mul(&one.add(&one.mul(delta["txt"])))
                        .mul(&one.mul(epsilon["txt"]).add(&tfh1h2["txt"].1 .1))
                        .mul(
                            &one.add(&one.mul(delta["txt"]))
                                .mul(epsilon["txt"])
                                .add(&tfh1h2["txt"].0 .1)
                                .add(&shift(&tfh1h2["txt"].0 .2).mul(delta["txt"])),
                        ),
                ),
            ),
            (&one.sub(&ln)).mul(
                &w["ip"]
                    .add(&w["ci"].mul(zeta[0]))
                    .add(&w["ni"].mul(zeta[0].pow([2 as u64])))
                    .sub(&tfh1h2["txt"].1 .1),
            ),
            z["txt"].1.sub(&one).mul(&l1),
            z["txt"].1.sub(&one).mul(&ln),
            // z_clk is computed from correct f_clk and takes expected extremal values
            (&one.sub(&ln)).mul(
                &(shift(&z["clk"].2)
                    .mul(
                        &one.add(&one.mul(delta["clk"]))
                            .mul(epsilon["clk"])
                            .add(&tfh1h2["clk"].2 .1)
                            .add(&tfh1h2["clk"].3 .1.mul(delta["clk"])),
                    )
                    .mul(
                        &one.add(&one.mul(delta["clk"]))
                            .mul(epsilon["clk"])
                            .add(&tfh1h2["clk"].3 .1)
                            .add(&shift(&tfh1h2["clk"].2 .2).mul(delta["clk"])),
                    ))
                .sub(
                    &(z["clk"].1)
                        .mul(&one.add(&one.mul(delta["clk"])))
                        .mul(&one.mul(epsilon["clk"]).add(&tfh1h2["clk"].1 .1))
                        .mul(
                            &one.add(&one.mul(delta["clk"]))
                                .mul(epsilon["clk"])
                                .add(&tfh1h2["clk"].0 .1)
                                .add(&shift(&tfh1h2["clk"].0 .2).mul(delta["clk"])),
                        ),
                ),
            ),
            (&one.sub(&ln)).mul(
                &one.sub(&shift(&p_w["mem_mp"]).sub(&w["mem_mp"]))
                    .mul(&w["delta_clk"].sub(&shift(&p_w["mem_clk"]).sub(&w["mem_clk"]))),
            ),
            (&one.sub(&ln)).mul(&(shift(&p_w["mem_mp"]).sub(&w["mem_mp"])).mul(&w["delta_clk"])),
            (&one.sub(&ln)).mul(
                &one.sub(&shift(&p_w["mem_mp"]).sub(&w["mem_mp"]))
                    .mul(&w["delta_clk"].sub(&tfh1h2["clk"].1 .1)),
            ),
            z["clk"].1.sub(&one).mul(&l1),
            z["clk"].1.sub(&one).mul(&ln),
            // z_opc is computed from correct f_opc and takes expected extremal values
            (&one.sub(&ln)).mul(
                &(shift(&z["opc"].2)
                    .mul(
                        &one.add(&one.mul(delta["opc"]))
                            .mul(epsilon["opc"])
                            .add(&tfh1h2["opc"].2 .1)
                            .add(&tfh1h2["opc"].3 .1.mul(delta["opc"])),
                    )
                    .mul(
                        &one.add(&one.mul(delta["opc"]))
                            .mul(epsilon["opc"])
                            .add(&tfh1h2["opc"].3 .1)
                            .add(&shift(&tfh1h2["opc"].2 .2).mul(delta["opc"])),
                    ))
                .sub(
                    &(z["opc"].1)
                        .mul(&one.add(&one.mul(delta["opc"])))
                        .mul(&one.mul(epsilon["opc"]).add(&tfh1h2["opc"].1 .1))
                        .mul(
                            &one.add(&one.mul(delta["opc"]))
                                .mul(epsilon["opc"])
                                .add(&tfh1h2["opc"].0 .1)
                                .add(&shift(&tfh1h2["opc"].0 .2).mul(delta["opc"])),
                        ),
                ),
            ),
            w["ci"]
                .add(&w["q_fjmp"].mul(zeta[1]))
                .add(&w["q_bjmp"].mul(zeta[1].pow([2 as u64])))
                .add(&w["q_add"].mul(zeta[1].pow([3 as u64])))
                .add(&w["q_sub"].mul(zeta[1].pow([4 as u64])))
                .add(&w["q_left"].mul(zeta[1].pow([5 as u64])))
                .add(&w["q_right"].mul(zeta[1].pow([6 as u64])))
                .add(&w["q_in"].mul(zeta[1].pow([7 as u64])))
                .add(&w["q_out"].mul(zeta[1].pow([8 as u64])))
                .sub(&tfh1h2["opc"].1 .1)
                .mul(&one.sub(&ln)),
            z["opc"].1.sub(&one).mul(&l1),
            z["opc"].1.sub(&one).mul(&ln),
            // clk ticks correctly
            (&one.sub(&ln)).mul(&shift(&p_w["clk"]).sub(&w["clk"]).sub(&one)),
            // mvz is computed correctly
            w["mvz"].sub(&one.sub(&w["mv"].mul(&w["inv"]))),
            w["mv"].mul(&one.sub(&w["mv"].mul(&w["inv"]))),
            // mem_mp increments by one or stays the same
            (&one.sub(&ln))
                .mul(&(shift(&p_w["mem_mp"]).sub(&w["mem_mp"])).mul(&shift(&p_w["mem_mv"]))),
            (&one.sub(&ln))
                .mul(&shift(&p_w["mem_mp"]).sub(&w["mem_mp"]))
                .mul(&shift(&p_w["mem_mp"]).sub(&w["mem_mp"]).sub(&one)),
            // [ instruction is executed correctly
            (&one.sub(&ln)).mul(
                &w["q_fjmp"].mul(
                    &(w["mv"].mul(&shift(&p_w["ip"]).sub(&w["ip"]).sub(&one.mul(Fr::from(1)))))
                        .add(&(shift(&p_w["ip"]).sub(&w["ni"])).mul(&w["mvz"])),
                ),
            ),
            (&one.sub(&ln)).mul(&w["q_fjmp"].mul(&shift(&p_w["mp"]).sub(&w["mp"]))),
            (&one.sub(&ln)).mul(&w["q_fjmp"].mul(&shift(&p_w["mv"]).sub(&w["mv"]))),
            // ] instruction is executed correctly
            (&one.sub(&ln)).mul(&w["q_bjmp"].mul(
                &(w["mv"].mul(&(shift(&p_w["ip"]).sub(&w["ni"])))).add(
                    &(shift(&p_w["ip"]).sub(&w["ip"]).sub(&one.mul(Fr::from(1)))).mul(&w["mvz"]),
                ),
            )),
            (&one.sub(&ln)).mul(&w["q_bjmp"].mul(&shift(&p_w["mp"]).sub(&w["mp"]))),
            (&one.sub(&ln)).mul(&w["q_bjmp"].mul(&shift(&p_w["mv"]).sub(&w["mv"]))),
            // < instruction executed correctly
            (&one.sub(&ln)).mul(&w["q_left"].mul(&(shift(&p_w["ip"]).sub(&w["ip"]).sub(&one)))),
            (&one.sub(&ln)).mul(&w["q_left"].mul(&shift(&p_w["mp"]).sub(&w["mp"]).add(&one))),
            // > instruction executed correctly
            (&one.sub(&ln)).mul(&w["q_right"].mul(&(shift(&p_w["ip"]).sub(&w["ip"]).sub(&one)))),
            (&one.sub(&ln)).mul(&w["q_right"].mul(&shift(&p_w["mp"]).sub(&w["mp"]).sub(&one))),
            // + instruction executed correctly
            (&one.sub(&ln)).mul(&w["q_add"].mul(&(shift(&p_w["ip"]).sub(&w["ip"]).sub(&one)))),
            (&one.sub(&ln)).mul(&w["q_add"].mul(&shift(&p_w["mv"]).sub(&w["mv"]).sub(&one))),
            (&one.sub(&ln)).mul(&w["q_add"].mul(&shift(&p_w["mp"]).sub(&w["mp"]))),
            // - instruction executed correctly
            (&one.sub(&ln)).mul(&w["q_sub"].mul(&(shift(&p_w["ip"]).sub(&w["ip"]).sub(&one)))),
            (&one.sub(&ln)).mul(&w["q_sub"].mul(&shift(&p_w["mv"]).sub(&w["mv"]).add(&one))),
            (&one.sub(&ln)).mul(&w["q_sub"].mul(&shift(&p_w["mp"]).sub(&w["mp"]))),
            // , instruction executed correctly
            (&one.sub(&ln)).mul(&w["q_in"].mul(&(shift(&p_w["ip"]).sub(&w["ip"]).sub(&one)))),
            (&one.sub(&ln)).mul(&w["q_in"].mul(&shift(&p_w["mp"]).sub(&w["mp"]))),
            // . instruction executed correctly
            (&one.sub(&ln)).mul(&w["q_out"].mul(&(shift(&p_w["ip"]).sub(&w["ip"]).sub(&one)))),
            (&one.sub(&ln)).mul(&w["q_out"].mul(&shift(&p_w["mv"]).sub(&w["mv"]))),
            (&one.sub(&ln)).mul(&w["q_out"].mul(&shift(&p_w["mp"]).sub(&w["mp"]))),
        ];

        let q = constraints
            .iter()
            .rev()
            .fold(
                Evaluations::from_vec_and_domain(vec![Fr::zero(); 8 * n], extended_domain),
                |acc, p| acc.mul(alpha).add(&p),
            )
            .interpolate();

        let (q, rem) = q.divide_by_vanishing_poly(domain).unwrap();
        assert_eq!(rem, DensePolynomial::zero());

        assert!(q.degree() < 3 * n + 6);
        let q_low = DensePolynomial::from_coefficients_vec(q.coeffs[0..n].to_vec()).add(
            DensePolynomial::from_coefficients_vec([vec![Fr::zero(); n], vec![b[0]]].concat()),
        );
        let q_mid = DensePolynomial::from_coefficients_vec(q.coeffs[n..(2 * n)].to_vec()).add(
            DensePolynomial::from_coefficients_vec(
                [vec![-b[0]], vec![Fr::zero(); n - 1], vec![b[1]]].concat(),
            ),
        );
        let q_high = DensePolynomial::from_coefficients_vec(q.coeffs[(2 * n)..].to_vec())
            .sub(&DensePolynomial::from_coefficients_vec(vec![b[1]]));

        [("low", &q_low), ("mid", &q_mid), ("high", &q_high)]
            .iter()
            .for_each(|(k, q)| {
                let com_q = kzg_commit(q, &cpi.srs);
                commitments.q.insert(k.to_string(), com_q);
            });
        transcript.append_commitments(
            b"round4",
            &commitments.q.values().copied().collect::<Vec<_>>(),
        );

        //
        // Round 5
        //
        let mu = transcript.challenge_scalars(1)[0];
        let omega = domain.group_gen;

        let l1_mu = l1.interpolate().evaluate(&mu);
        let ln_mu = ln.interpolate().evaluate(&mu);
        let zh_mu = domain.vanishing_polynomial().evaluate(&mu);

        let e_w: BTreeMap<&str, Fr> = [
            ("clk", p_w["clk"].evaluate(&mu)),
            ("o_clk", p_w["clk"].evaluate(&(mu * omega))),
            ("ip", p_w["ip"].evaluate(&mu)),
            ("o_ip", p_w["ip"].evaluate(&(mu * omega))),
            ("ni", p_w["ni"].evaluate(&mu)),
            ("mp", p_w["mp"].evaluate(&mu)),
            ("o_mp", p_w["mp"].evaluate(&(mu * omega))),
            ("mv", p_w["mv"].evaluate(&mu)),
            ("o_mv", p_w["mv"].evaluate(&(mu * omega))),
            ("mvz", p_w["mvz"].evaluate(&mu)),
            ("o_mem_clk", p_w["mem_clk"].evaluate(&(mu * omega))),
            ("mem_mp", p_w["mem_mp"].evaluate(&mu)),
            ("o_mem_mp", p_w["mem_mp"].evaluate(&(mu * omega))),
            ("o_mem_mv", p_w["mem_mv"].evaluate(&(mu * omega))),
        ]
        .into();
        transcript.append_evaluations(b"round5", &e_w.values().cloned().collect::<Vec<_>>());
        opening_evaluations.witness = e_w.iter().map(|(k, v)| (k.to_string(), *v)).collect();

        let e_z: BTreeMap<&str, Fr> = [
            ("out", z["out"].2.evaluate(&mu)),
            ("o_out", z["out"].2.evaluate(&(mu * omega))),
            ("in", z["in"].2.evaluate(&mu)),
            ("o_in", z["in"].2.evaluate(&(mu * omega))),
            ("o_mem", z["mem"].2.evaluate(&(mu * omega))),
            ("o_txt", z["txt"].2.evaluate(&(mu * omega))),
            ("o_clk", z["clk"].2.evaluate(&(mu * omega))),
            ("o_opc", z["opc"].2.evaluate(&(mu * omega))),
        ]
        .into();
        transcript.append_evaluations(b"round5", &e_z.values().cloned().collect::<Vec<_>>());
        opening_evaluations.z = e_z.iter().map(|(k, v)| (k.to_string(), *v)).collect();

        let e_ttfh1h2 = tfh1h2
            .iter()
            .map(
                |(&k, ((_, _, p_t), (_, _, p_f), (_, _, p_h1), (_, _, p_h2)))| {
                    let e_t = p_t.evaluate(&mu);
                    let e_ot = p_t.evaluate(&(mu * omega));
                    let e_f = p_f.evaluate(&mu);
                    let e_oh1 = p_h1.evaluate(&(mu * omega));
                    let e_h2 = p_h2.evaluate(&mu);
                    transcript.append_evaluations(b"round5", &[e_t, e_ot, e_f, e_oh1, e_h2]);
                    opening_evaluations
                        .ttfh1h2
                        .insert(k.to_string(), [e_t, e_ot, e_f, e_oh1, e_h2]);

                    (k, (e_t, e_ot, e_f, e_oh1, e_h2))
                },
            )
            .collect::<BTreeMap<&str, (Fr, Fr, Fr, Fr, Fr)>>();

        //
        // Round 6
        //
        let nu = transcript.challenge_scalars(1)[0];

        let one = one.interpolate();
        let linearised_constraints = vec![
            one.mul(e_z["o_out"])
                .sub(&p_w["q_out"].mul(e_w["mv"] + xi[9] * e_z["out"]))
                .sub(&one.sub(&p_w["q_out"]).mul(e_z["out"]))
                .mul(Fr::one() - ln_mu),
            one.mul(l1_mu * e_z["out"]),
            one.mul(ln_mu * (e_z["out"] - terminal_out)),
            one.mul(e_z["o_in"])
                .sub(&p_w["q_in"].mul(e_w["mv"] + xi[8] * e_z["in"]))
                .sub(&one.sub(&p_w["q_in"]).mul(e_z["in"]))
                .mul(Fr::one() - ln_mu),
            one.mul(l1_mu * e_z["in"]),
            one.mul(ln_mu * (e_z["in"] - terminal_in)),
            one.mul(gamma + e_w["mem_mp"])
                .add(p_w["mem_clk"].mul(beta))
                .add(p_w["mem_mv"].mul(beta.pow([2 as u64])))
                .mul((Fr::one() - ln_mu) * e_z["o_mem"])
                .sub(&z["mem"].2.mul(
                    (Fr::one() - ln_mu)
                        * (gamma
                            + e_w["mp"]
                            + beta * e_w["clk"]
                            + beta.pow([2 as u64]) * e_w["mv"]),
                )),
            z["mem"].2.sub(&one).mul(l1_mu),
            z["mem"].2.sub(&one).mul(ln_mu),
            (&tfh1h2["txt"].2 .2)
                .add(&one.mul(
                    epsilon["txt"] * (Fr::one() + delta["txt"]) + delta["txt"] * e_ttfh1h2["txt"].4,
                ))
                .mul(
                    e_z["o_txt"]
                        * (epsilon["txt"] * (Fr::one() + delta["txt"])
                            + delta["txt"] * e_ttfh1h2["txt"].3
                            + e_ttfh1h2["txt"].4),
                )
                .sub(&z["txt"].2.mul(
                    (Fr::one() + delta["txt"])
                        * (epsilon["txt"] + e_ttfh1h2["txt"].2)
                        * (epsilon["txt"] * (Fr::one() + delta["txt"])
                            + e_ttfh1h2["txt"].0
                            + delta["txt"] * e_ttfh1h2["txt"].1),
                ))
                .mul(Fr::one() - ln_mu),
            p_w["ci"]
                .mul(zeta[0])
                .add(one.mul(e_w["ip"] + e_w["ni"] * zeta[0].pow([2 as u64]) - e_ttfh1h2["txt"].2))
                .mul(Fr::one() - ln_mu),
            z["txt"].2.sub(&one).mul(l1_mu),
            z["txt"].2.sub(&one).mul(ln_mu),
            (&tfh1h2["clk"].2 .2)
                .add(&one.mul(
                    epsilon["clk"] * (Fr::one() + delta["clk"]) + delta["clk"] * e_ttfh1h2["clk"].4,
                ))
                .mul(
                    e_z["o_clk"]
                        * (epsilon["clk"] * (Fr::one() + delta["clk"])
                            + delta["clk"] * e_ttfh1h2["clk"].3
                            + e_ttfh1h2["clk"].4),
                )
                .sub(&z["clk"].2.mul(
                    (Fr::one() + delta["clk"])
                        * (epsilon["clk"] + e_ttfh1h2["clk"].2)
                        * (epsilon["clk"] * (Fr::one() + delta["clk"])
                            + e_ttfh1h2["clk"].0
                            + delta["clk"] * e_ttfh1h2["clk"].1),
                ))
                .mul(Fr::one() - ln_mu),
            (&p_w["delta_clk"].sub(&one.mul(e_w["o_mem_clk"])))
                .add(&p_w["mem_clk"])
                .mul((Fr::one() - ln_mu) * (Fr::one() - e_w["o_mem_mp"] + e_w["mem_mp"])),
            p_w["delta_clk"].mul((Fr::one() - ln_mu) * (e_w["o_mem_mp"] - e_w["mem_mp"])),
            p_w["delta_clk"]
                .sub(&one.mul(e_ttfh1h2["clk"].2))
                .mul((Fr::one() - ln_mu) * (Fr::one() - e_w["o_mem_mp"] + e_w["mem_mp"])),
            z["clk"].2.sub(&one).mul(l1_mu),
            z["clk"].2.sub(&one).mul(ln_mu),
            (&tfh1h2["opc"].2 .2)
                .add(&one.mul(
                    epsilon["opc"] * (Fr::one() + delta["opc"]) + delta["opc"] * e_ttfh1h2["opc"].4,
                ))
                .mul(
                    e_z["o_opc"]
                        * (epsilon["opc"] * (Fr::one() + delta["opc"])
                            + delta["opc"] * e_ttfh1h2["opc"].3
                            + e_ttfh1h2["opc"].4),
                )
                .sub(&z["opc"].2.mul(
                    (Fr::one() + delta["opc"])
                        * (epsilon["opc"] + e_ttfh1h2["opc"].2)
                        * (epsilon["opc"] * (Fr::one() + delta["opc"])
                            + e_ttfh1h2["opc"].0
                            + delta["opc"] * e_ttfh1h2["opc"].1),
                ))
                .mul(Fr::one() - ln_mu),
            (&p_w["ci"])
                .add(&p_w["q_fjmp"].mul(zeta[1]))
                .add(p_w["q_bjmp"].mul(zeta[1].pow([2 as u64])))
                .add(p_w["q_add"].mul(zeta[1].pow([3 as u64])))
                .add(p_w["q_sub"].mul(zeta[1].pow([4 as u64])))
                .add(p_w["q_left"].mul(zeta[1].pow([5 as u64])))
                .add(p_w["q_right"].mul(zeta[1].pow([6 as u64])))
                .add(p_w["q_in"].mul(zeta[1].pow([7 as u64])))
                .add(p_w["q_out"].mul(zeta[1].pow([8 as u64])))
                .sub(&one.mul(e_ttfh1h2["opc"].2))
                .mul(Fr::one() - ln_mu),
            z["opc"].2.sub(&one).mul(l1_mu),
            z["opc"].2.sub(&one).mul(ln_mu),
            (&p_w["clk"])
                .sub(&one.mul(e_w["o_clk"] - Fr::one()))
                .mul(-(Fr::one() - ln_mu)),
            one.mul(e_w["mvz"])
                .sub(&one.sub(&p_w["inv"].mul(e_w["mv"]))),
            one.sub(&p_w["inv"].mul(e_w["mv"])).mul(e_w["mv"]),
            one.mul((Fr::one() - ln_mu) * (e_w["o_mem_mp"] - e_w["mem_mp"]) * e_w["o_mem_mv"]),
            one.mul(
                (Fr::one() - ln_mu)
                    * (e_w["o_mem_mp"] - e_w["mem_mp"])
                    * (e_w["o_mem_mp"] - e_w["mem_mp"] - Fr::one()),
            ),
            p_w["q_fjmp"].mul(
                (Fr::one() - ln_mu)
                    * (e_w["mv"] * (e_w["o_ip"] - e_w["ip"] - Fr::one())
                        + e_w["mvz"] * (e_w["o_ip"] - e_w["ni"])),
            ),
            p_w["q_fjmp"].mul((Fr::one() - ln_mu) * (e_w["o_mp"] - e_w["mp"])),
            p_w["q_fjmp"].mul((Fr::one() - ln_mu) * (e_w["o_mv"] - e_w["mv"])),
            p_w["q_bjmp"].mul(
                (Fr::one() - ln_mu)
                    * (e_w["mvz"] * (e_w["o_ip"] - e_w["ip"] - Fr::one())
                        + e_w["mv"] * (e_w["o_ip"] - e_w["ni"])),
            ),
            p_w["q_bjmp"].mul((Fr::one() - ln_mu) * (e_w["o_mp"] - e_w["mp"])),
            p_w["q_bjmp"].mul((Fr::one() - ln_mu) * (e_w["o_mv"] - e_w["mv"])),
            p_w["q_left"].mul((Fr::one() - ln_mu) * (e_w["o_ip"] - e_w["ip"] - Fr::one())),
            p_w["q_left"].mul((Fr::one() - ln_mu) * (e_w["o_mp"] - e_w["mp"] + Fr::one())),
            p_w["q_right"].mul((Fr::one() - ln_mu) * (e_w["o_ip"] - e_w["ip"] - Fr::one())),
            p_w["q_right"].mul((Fr::one() - ln_mu) * (e_w["o_mp"] - e_w["mp"] - Fr::one())),
            p_w["q_add"].mul((Fr::one() - ln_mu) * (e_w["o_ip"] - e_w["ip"] - Fr::one())),
            p_w["q_add"].mul((Fr::one() - ln_mu) * (e_w["o_mv"] - e_w["mv"] - Fr::one())),
            p_w["q_add"].mul((Fr::one() - ln_mu) * (e_w["o_mp"] - e_w["mp"])),
            p_w["q_sub"].mul((Fr::one() - ln_mu) * (e_w["o_ip"] - e_w["ip"] - Fr::one())),
            p_w["q_sub"].mul((Fr::one() - ln_mu) * (e_w["o_mv"] - e_w["mv"] + Fr::one())),
            p_w["q_sub"].mul((Fr::one() - ln_mu) * (e_w["o_mp"] - e_w["mp"])),
            p_w["q_in"].mul((Fr::one() - ln_mu) * (e_w["o_ip"] - e_w["ip"] - Fr::one())),
            p_w["q_in"].mul((Fr::one() - ln_mu) * (e_w["o_mp"] - e_w["mp"])),
            p_w["q_out"].mul((Fr::one() - ln_mu) * (e_w["o_ip"] - e_w["ip"] - Fr::one())),
            p_w["q_out"].mul((Fr::one() - ln_mu) * (e_w["o_mv"] - e_w["mv"])),
            p_w["q_out"].mul((Fr::one() - ln_mu) * (e_w["o_mp"] - e_w["mp"])),
        ];
        assert_eq!(constraints.len(), linearised_constraints.len());

        let r = linearised_constraints
            .iter()
            .rev()
            .fold(DensePolynomial::zero(), |acc, p| (&acc.mul(alpha)).add(p))
            .sub(
                &q_low
                    .add(q_mid.mul(mu.pow([n as u64])))
                    .add(q_high.mul(mu.pow([2 * n as u64])))
                    .mul(zh_mu),
            );
        assert_eq!(r.evaluate(&mu), Fr::zero());

        let w_mu = r
            .clone()
            .add(p_w["clk"].sub(&one.mul(e_w["clk"])).mul(nu))
            .add(p_w["ip"].sub(&one.mul(e_w["ip"])).mul(nu.pow([2 as u64])))
            .add(p_w["ni"].sub(&one.mul(e_w["ni"])).mul(nu.pow([3 as u64])))
            .add(p_w["mp"].sub(&one.mul(e_w["mp"])).mul(nu.pow([4 as u64])))
            .add(p_w["mv"].sub(&one.mul(e_w["mv"])).mul(nu.pow([5 as u64])))
            .add(p_w["mvz"].sub(&one.mul(e_w["mvz"])).mul(nu.pow([6 as u64])))
            .add(
                p_w["mem_mp"]
                    .sub(&one.mul(e_w["mem_mp"]))
                    .mul(nu.pow([7 as u64])),
            )
            .add(z["out"].2.sub(&one.mul(e_z["out"])).mul(nu.pow([8 as u64])))
            .add(z["in"].2.sub(&one.mul(e_z["in"])).mul(nu.pow([9 as u64])))
            .add(
                tfh1h2["txt"]
                    .0
                     .2
                    .sub(&one.mul(e_ttfh1h2["txt"].0))
                    .mul(nu.pow([10 as u64])),
            )
            .add(
                tfh1h2["txt"]
                    .1
                     .2
                    .sub(&one.mul(e_ttfh1h2["txt"].2))
                    .mul(nu.pow([11 as u64])),
            )
            .add(
                tfh1h2["txt"]
                    .3
                     .2
                    .sub(&one.mul(e_ttfh1h2["txt"].4))
                    .mul(nu.pow([12 as u64])),
            )
            .add(
                tfh1h2["clk"]
                    .0
                     .2
                    .sub(&one.mul(e_ttfh1h2["clk"].0))
                    .mul(nu.pow([13 as u64])),
            )
            .add(
                tfh1h2["clk"]
                    .1
                     .2
                    .sub(&one.mul(e_ttfh1h2["clk"].2))
                    .mul(nu.pow([14 as u64])),
            )
            .add(
                tfh1h2["clk"]
                    .3
                     .2
                    .sub(&one.mul(e_ttfh1h2["clk"].4))
                    .mul(nu.pow([15 as u64])),
            )
            .add(
                tfh1h2["opc"]
                    .0
                     .2
                    .sub(&one.mul(e_ttfh1h2["opc"].0))
                    .mul(nu.pow([16 as u64])),
            )
            .add(
                tfh1h2["opc"]
                    .1
                     .2
                    .sub(&one.mul(e_ttfh1h2["opc"].2))
                    .mul(nu.pow([17 as u64])),
            )
            .add(
                tfh1h2["opc"]
                    .3
                     .2
                    .sub(&one.mul(e_ttfh1h2["opc"].4))
                    .mul(nu.pow([18 as u64])),
            )
            .div(&DensePolynomial::from_coefficients_vec(vec![
                -mu,
                Fr::one(),
            ]));

        let w_omu = p_w["clk"]
            .sub(&one.mul(e_w["o_clk"]))
            .add(p_w["ip"].sub(&one.mul(e_w["o_ip"])).mul(nu))
            .add(p_w["mp"].sub(&one.mul(e_w["o_mp"])).mul(nu.pow([2 as u64])))
            .add(p_w["mv"].sub(&one.mul(e_w["o_mv"])).mul(nu.pow([3 as u64])))
            .add(
                p_w["mem_clk"]
                    .sub(&one.mul(e_w["o_mem_clk"]))
                    .mul(nu.pow([4 as u64])),
            )
            .add(
                p_w["mem_mp"]
                    .sub(&one.mul(e_w["o_mem_mp"]))
                    .mul(nu.pow([5 as u64])),
            )
            .add(
                p_w["mem_mv"]
                    .sub(&one.mul(e_w["o_mem_mv"]))
                    .mul(nu.pow([6 as u64])),
            )
            .add(
                z["out"]
                    .2
                    .sub(&one.mul(e_z["o_out"]))
                    .mul(nu.pow([7 as u64])),
            )
            .add(z["in"].2.sub(&one.mul(e_z["o_in"])).mul(nu.pow([8 as u64])))
            .add(
                z["mem"]
                    .2
                    .sub(&one.mul(e_z["o_mem"]))
                    .mul(nu.pow([9 as u64])),
            )
            .add(
                z["txt"]
                    .2
                    .sub(&one.mul(e_z["o_txt"]))
                    .mul(nu.pow([10 as u64])),
            )
            .add(
                z["clk"]
                    .2
                    .sub(&one.mul(e_z["o_clk"]))
                    .mul(nu.pow([11 as u64])),
            )
            .add(
                z["opc"]
                    .2
                    .sub(&one.mul(e_z["o_opc"]))
                    .mul(nu.pow([12 as u64])),
            )
            .add(
                tfh1h2["txt"]
                    .0
                     .2
                    .sub(&one.mul(e_ttfh1h2["txt"].1))
                    .mul(nu.pow([13 as u64])),
            )
            .add(
                tfh1h2["txt"]
                    .2
                     .2
                    .sub(&one.mul(e_ttfh1h2["txt"].3))
                    .mul(nu.pow([14 as u64])),
            )
            .add(
                tfh1h2["clk"]
                    .0
                     .2
                    .sub(&one.mul(e_ttfh1h2["clk"].1))
                    .mul(nu.pow([15 as u64])),
            )
            .add(
                tfh1h2["clk"]
                    .2
                     .2
                    .sub(&one.mul(e_ttfh1h2["clk"].3))
                    .mul(nu.pow([16 as u64])),
            )
            .add(
                tfh1h2["opc"]
                    .0
                     .2
                    .sub(&one.mul(e_ttfh1h2["opc"].1))
                    .mul(nu.pow([17 as u64])),
            )
            .add(
                tfh1h2["opc"]
                    .2
                     .2
                    .sub(&one.mul(e_ttfh1h2["opc"].3))
                    .mul(nu.pow([18 as u64])),
            )
            .div(&DensePolynomial::from_coefficients_vec(vec![
                -mu * omega,
                Fr::one(),
            ]));

        let com_w_mu = kzg_commit(&w_mu, &cpi.srs);
        let com_w_omu = kzg_commit(&w_omu, &cpi.srs);
        commitments.w.insert("mu".to_string(), com_w_mu);
        commitments.w.insert("omega_mu".to_string(), com_w_omu);

        Self {
            commitments,
            opening_evaluations,
        }
    }
}
