use std::collections::BTreeMap;

use ark_bls12_381::Bls12_381;
use ark_ec::{pairing::Pairing, Group};
use ark_ff::Field;
use ark_std::{One, Zero};
use merlin::Transcript;

use crate::{
    preprocessing::PreprocessedInputs, prover::Proof, transcript::TranscriptProtocol, Fr, G1,
};

/// Verify the correcteness of a given `Proof`, together with corresponding `PreprocessedInputs`.
pub fn verify(proof: &Proof, ppi: &PreprocessedInputs) -> bool {
    let commitments = proof.commitments();
    let openings = proof.opening_evaluations();
    let mut transcript = Transcript::new(b"BrainPlonk");
    transcript.init(ppi.cpi());

    // 1. Validate that the commitments are are in G1
    if !commitments.validate() {
        return false;
    }

    // 4. Compute the challenges from the transcript
    transcript.append_commitments(
        b"round1",
        &commitments.witness().values().copied().collect::<Vec<_>>(),
    );
    let zeta = transcript.challenge_scalars(2);

    commitments.fh1h2().values().for_each(|coms| {
        transcript.append_commitments(b"round2", coms);
    });
    let xi = transcript.challenge_scalars(10);
    let beta = xi[0];
    let gamma = xi[1];
    let (delta, epsilon): (BTreeMap<&str, _>, BTreeMap<&str, _>) = commitments
        .fh1h2()
        .iter()
        .enumerate()
        .map(|(j, (k, _))| ((k.as_str(), xi[2 * j + 2]), (k.as_str(), xi[2 * j + 3])))
        .unzip();

    transcript.append_commitments(
        b"round3",
        &commitments.z().values().copied().collect::<Vec<_>>(),
    );
    let alpha = transcript.challenge_scalars(1)[0];

    transcript.append_commitments(
        b"round4",
        &commitments.q().values().copied().collect::<Vec<_>>(),
    );
    let mu = transcript.challenge_scalars(1)[0];

    transcript.append_evaluations(
        b"round5",
        &openings.witness().values().cloned().collect::<Vec<_>>(),
    );
    transcript.append_evaluations(
        b"round5",
        &openings.z().values().cloned().collect::<Vec<_>>(),
    );
    openings.ttfh1h2().iter().for_each(|(_, evals)| {
        transcript.append_evaluations(b"round5", evals);
    });
    let nu = transcript.challenge_scalars(1)[0];

    transcript.append_commitments(
        b"round6",
        &commitments.w().values().copied().collect::<Vec<_>>(),
    );
    let eta = transcript.challenge_scalars(1)[0];

    // 5. Compute the zero polynomial evaluation
    let n = ppi.cpi().n as u64;
    let h = ppi.cpi().domain.offset;
    let h_pow = (
        ppi.cpi().domain.offset_pow_size * ppi.cpi().domain.offset_inv,
        ppi.cpi().domain.offset_pow_size,
    );
    let g_pow = ppi.cpi().domain.group_gen_inv;
    let zh_mu = mu.pow([n]) - h_pow.1;

    // 6. Compute the Lagrange polynomials evaluations
    let l1_mu = zh_mu / (Fr::from(n) * h_pow.0 * (mu - h));
    let ln_mu = (zh_mu * g_pow) / (Fr::from(n) * h_pow.0 * (mu - h * g_pow));

    // 8. Compute the public tables commitments
    let com_prog_text = ppi.vpi().com_prog_text.0
        + ppi.vpi().com_prog_text.1 * zeta[0]
        + ppi.vpi().com_prog_text.2 * zeta[0].pow([2 as u64]);
    let com_opc_table = ppi
        .vpi()
        .com_opc_table
        .1
        .iter()
        .enumerate()
        .fold(ppi.vpi().com_opc_table.0, |acc, (i, &e)| {
            acc + e * zeta[1].pow([i as u64 + 1])
        });
    let com_clk_table = ppi.vpi().com_clk_table;

    // 9. Compute r(X)'s constant term
    let terminal_in = ppi
        .cpi()
        .in_table
        .iter()
        .fold(Fr::zero(), |acc, &v| v + xi[8] * acc);
    let terminal_out = ppi
        .cpi()
        .out_table
        .iter()
        .fold(Fr::zero(), |acc, &v| v + xi[9] * acc);
    let z = openings.z();
    let w = openings.witness();
    let ttfh1h2 = openings.ttfh1h2();

    let r0 = vec![
        (Fr::one() - ln_mu) * (z["o_out"] - z["out"]),
        l1_mu * z["out"],
        ln_mu * (z["out"] - terminal_out),
        (Fr::one() - ln_mu) * (z["o_in"] - z["in"]),
        l1_mu * z["in"],
        ln_mu * (z["in"] - terminal_in),
        (Fr::one() - ln_mu) * z["o_mem"] * (w["mem_mp"] + gamma),
        -l1_mu,
        -ln_mu,
        (Fr::one() - ln_mu)
            * z["o_txt"]
            * (epsilon["txt"] * (Fr::one() + delta["txt"]) + delta["txt"] * ttfh1h2["txt"][4])
            * (epsilon["txt"] * (Fr::one() + delta["txt"])
                + delta["txt"] * ttfh1h2["txt"][3]
                + ttfh1h2["txt"][4]),
        (Fr::one() - ln_mu) * (w["ip"] + zeta[0].pow([2 as u64]) * w["ni"] - ttfh1h2["txt"][2]),
        -l1_mu,
        -ln_mu,
        (Fr::one() - ln_mu)
            * z["o_clk"]
            * (epsilon["clk"] * (Fr::one() + delta["clk"]) + delta["clk"] * ttfh1h2["clk"][4])
            * (epsilon["clk"] * (Fr::one() + delta["clk"])
                + delta["clk"] * ttfh1h2["clk"][3]
                + ttfh1h2["clk"][4]),
        -(Fr::one() - ln_mu) * (Fr::one() - w["o_mem_mp"] + w["mem_mp"]) * w["o_mem_clk"],
        Fr::zero(),
        -(Fr::one() - ln_mu) * (Fr::one() - w["o_mem_mp"] + w["mem_mp"]) * ttfh1h2["clk"][2],
        -l1_mu,
        -ln_mu,
        (Fr::one() - ln_mu)
            * z["o_opc"]
            * (epsilon["opc"] * (Fr::one() + delta["opc"]) + delta["opc"] * ttfh1h2["opc"][4])
            * (epsilon["opc"] * (Fr::one() + delta["opc"])
                + delta["opc"] * ttfh1h2["opc"][3]
                + ttfh1h2["opc"][4]),
        -(Fr::one() - ln_mu) * ttfh1h2["opc"][2],
        -l1_mu,
        -ln_mu,
        (Fr::one() - ln_mu) * (w["o_clk"] - Fr::one()),
        w["mvz"] - Fr::one(),
        w["mv"],
        (Fr::one() - ln_mu) * (w["o_mem_mp"] - w["mem_mp"]) * w["o_mem_mv"],
        (Fr::one() - ln_mu)
            * (w["o_mem_mp"] - w["mem_mp"])
            * (w["o_mem_mp"] - w["mem_mp"] - Fr::one()),
    ]
    .iter()
    .rev()
    .fold(Fr::zero(), |acc, &e| e + acc * alpha);

    // 10. Compute the first part of the batched polynomial commitment
    let com_z = commitments.z();
    let com_w = commitments.witness();
    let com_fh1h2 = commitments.fh1h2();
    let com_q = commitments.q();

    let d1 = com_w["q_out"]
        * ((Fr::one() - ln_mu) * (z["out"] - (w["mv"] + xi[9] * z["out"]))
            + (Fr::one() - ln_mu) * (w["o_ip"] - w["ip"] - Fr::one()) * alpha.pow([46 as u64])
            + (Fr::one() - ln_mu) * (w["o_mv"] - w["mv"]) * alpha.pow([47 as u64])
            + (Fr::one() - ln_mu) * (w["o_mp"] - w["mp"]) * alpha.pow([48 as u64])
            + (Fr::one() - ln_mu) * (zeta[1].pow([8 as u64])) * alpha.pow([20 as u64]))
        + com_w["q_in"]
            * ((Fr::one() - ln_mu)
                * (z["in"] - (w["mv"] + xi[8] * z["in"]))
                * alpha.pow([3 as u64])
                + (Fr::one() - ln_mu) * (w["o_ip"] - w["ip"] - Fr::one()) * alpha.pow([44 as u64])
                + (Fr::one() - ln_mu) * (w["o_mp"] - w["mp"]) * alpha.pow([45 as u64])
                + (Fr::one() - ln_mu) * (zeta[1].pow([7 as u64])) * alpha.pow([20 as u64]))
        + com_w["mem_clk"]
            * ((Fr::one() - ln_mu) * (beta * z["o_mem"]) * alpha.pow([6 as u64])
                + (Fr::one() - ln_mu)
                    * (Fr::one() - w["o_mem_mp"] + w["mem_mp"])
                    * alpha.pow([14 as u64]))
        + com_w["mem_mv"]
            * (Fr::one() - ln_mu)
            * beta.pow([2 as u64])
            * z["o_mem"]
            * alpha.pow([6 as u64])
        + com_z["mem"]
            * ((ln_mu - Fr::one())
                * (w["mp"] + beta * w["clk"] + beta.pow([2 as u64]) * w["mv"] + gamma)
                * alpha.pow([6 as u64])
                + l1_mu * alpha.pow([7 as u64])
                + ln_mu * alpha.pow([8 as u64]))
        + com_fh1h2["txt"][1]
            * (Fr::one() - ln_mu)
            * z["o_txt"]
            * (epsilon["txt"] * (Fr::one() + delta["txt"])
                + ttfh1h2["txt"][4]
                + delta["txt"] * ttfh1h2["txt"][3])
            * alpha.pow([9 as u64])
        + com_z["txt"]
            * ((ln_mu - Fr::one())
                * (Fr::one() + delta["txt"])
                * (epsilon["txt"] + ttfh1h2["txt"][2])
                * (epsilon["txt"] * (Fr::one() + delta["txt"])
                    + ttfh1h2["txt"][0]
                    + delta["txt"] * ttfh1h2["txt"][1])
                * alpha.pow([9 as u64])
                + l1_mu * alpha.pow([11 as u64])
                + ln_mu * alpha.pow([12 as u64]))
        + com_w["ci"]
            * ((Fr::one() - ln_mu) * (zeta[0]) * alpha.pow([10 as u64])
                + (Fr::one() - ln_mu) * alpha.pow([20 as u64]))
        + com_fh1h2["clk"][1]
            * (Fr::one() - ln_mu)
            * z["o_clk"]
            * (epsilon["clk"] * (Fr::one() + delta["clk"])
                + ttfh1h2["clk"][4]
                + delta["clk"] * ttfh1h2["clk"][3])
            * alpha.pow([13 as u64])
        + com_z["clk"]
            * ((ln_mu - Fr::one())
                * (Fr::one() + delta["clk"])
                * (epsilon["clk"] + ttfh1h2["clk"][2])
                * (epsilon["clk"] * (Fr::one() + delta["clk"])
                    + ttfh1h2["clk"][0]
                    + delta["clk"] * ttfh1h2["clk"][1])
                * alpha.pow([13 as u64])
                + l1_mu * alpha.pow([17 as u64])
                + ln_mu * alpha.pow([18 as u64]))
        + com_w["delta_clk"]
            * ((Fr::one() - ln_mu)
                * (Fr::one() - w["o_mem_mp"] + w["mem_mp"])
                * alpha.pow([14 as u64])
                + (Fr::one() - ln_mu) * (w["o_mem_mp"] - w["mem_mp"]) * alpha.pow([15 as u64])
                + (Fr::one() - ln_mu)
                    * (Fr::one() - w["o_mem_mp"] + w["mem_mp"])
                    * alpha.pow([16 as u64]))
        + com_fh1h2["opc"][1]
            * (Fr::one() - ln_mu)
            * z["o_opc"]
            * (epsilon["opc"] * (Fr::one() + delta["opc"])
                + ttfh1h2["opc"][4]
                + delta["opc"] * ttfh1h2["opc"][3])
            * alpha.pow([19 as u64])
        + com_z["opc"]
            * ((ln_mu - Fr::one())
                * (Fr::one() + delta["opc"])
                * (epsilon["opc"] + ttfh1h2["opc"][2])
                * (epsilon["opc"] * (Fr::one() + delta["opc"])
                    + ttfh1h2["opc"][0]
                    + delta["opc"] * ttfh1h2["opc"][1])
                * alpha.pow([19 as u64])
                + l1_mu * alpha.pow([21 as u64])
                + ln_mu * alpha.pow([22 as u64]))
        + com_w["q_fjmp"]
            * ((Fr::one() - ln_mu) * (zeta[1]) * alpha.pow([20 as u64])
                + (Fr::one() - ln_mu)
                    * (w["mv"] * (w["o_ip"] - w["ip"] - Fr::one())
                        + w["mvz"] * (w["o_ip"] - w["ni"]))
                    * alpha.pow([28 as u64])
                + (Fr::one() - ln_mu) * (w["o_mp"] - w["mp"]) * alpha.pow([29 as u64])
                + (Fr::one() - ln_mu) * (w["o_mv"] - w["mv"]) * alpha.pow([30 as u64]))
        + com_w["q_bjmp"]
            * ((Fr::one() - ln_mu) * (zeta[1].pow([2 as u64])) * alpha.pow([20 as u64])
                + (Fr::one() - ln_mu)
                    * (w["mv"] * (w["o_ip"] - w["ni"])
                        + w["mvz"] * (w["o_ip"] - w["ip"] - Fr::one()))
                    * alpha.pow([31 as u64])
                + (Fr::one() - ln_mu) * (w["o_mp"] - w["mp"]) * alpha.pow([32 as u64])
                + (Fr::one() - ln_mu) * (w["o_mv"] - w["mv"]) * alpha.pow([33 as u64]))
        + com_w["q_add"]
            * ((Fr::one() - ln_mu) * (zeta[1].pow([3 as u64])) * alpha.pow([20 as u64])
                + (Fr::one() - ln_mu) * (w["o_ip"] - w["ip"] - Fr::one()) * alpha.pow([38 as u64])
                + (Fr::one() - ln_mu) * (w["o_mv"] - w["mv"] - Fr::one()) * alpha.pow([39 as u64])
                + (Fr::one() - ln_mu) * (w["o_mp"] - w["mp"]) * alpha.pow([40 as u64]))
        + com_w["q_sub"]
            * ((Fr::one() - ln_mu) * (zeta[1].pow([4 as u64])) * alpha.pow([20 as u64])
                + (Fr::one() - ln_mu) * (w["o_ip"] - w["ip"] - Fr::one()) * alpha.pow([41 as u64])
                + (Fr::one() - ln_mu) * (w["o_mv"] - w["mv"] + Fr::one()) * alpha.pow([42 as u64])
                + (Fr::one() - ln_mu) * (w["o_mp"] - w["mp"]) * alpha.pow([43 as u64]))
        + com_w["q_left"]
            * ((Fr::one() - ln_mu) * (zeta[1].pow([5 as u64])) * alpha.pow([20 as u64])
                + (Fr::one() - ln_mu) * (w["o_ip"] - w["ip"] - Fr::one()) * alpha.pow([34 as u64])
                + (Fr::one() - ln_mu) * (w["o_mp"] - w["mp"] + Fr::one()) * alpha.pow([35 as u64]))
        + com_w["q_right"]
            * ((Fr::one() - ln_mu) * (zeta[1].pow([6 as u64])) * alpha.pow([20 as u64])
                + (Fr::one() - ln_mu) * (w["o_ip"] - w["ip"] - Fr::one()) * alpha.pow([36 as u64])
                + (Fr::one() - ln_mu) * (w["o_mp"] - w["mp"] - Fr::one()) * alpha.pow([37 as u64]))
        + com_w["clk"] * (ln_mu - Fr::one()) * alpha.pow([23 as u64])
        + com_w["inv"]
            * (w["mv"] * alpha.pow([24 as u64])
                + (-w["mv"].pow([2 as u64])) * alpha.pow([25 as u64]))
        + com_q["low"] * (-zh_mu)
        + com_q["mid"] * (-zh_mu * mu.pow([n]))
        + com_q["high"] * (-zh_mu * mu.pow([2 * n]));

    // 11. Compute the full batched polynomial commitment
    let f1 = d1
        + com_w["clk"] * nu
        + com_w["ip"] * nu.pow([2 as u64])
        + com_w["ni"] * nu.pow([3 as u64])
        + com_w["mp"] * nu.pow([4 as u64])
        + com_w["mv"] * nu.pow([5 as u64])
        + com_w["mvz"] * nu.pow([6 as u64])
        + com_w["mem_mp"] * nu.pow([7 as u64])
        + com_z["out"] * nu.pow([8 as u64])
        + com_z["in"] * nu.pow([9 as u64])
        + com_prog_text * nu.pow([10 as u64])
        + com_fh1h2["txt"][0] * nu.pow([11 as u64])
        + com_fh1h2["txt"][2] * nu.pow([12 as u64])
        + com_clk_table * nu.pow([13 as u64])
        + com_fh1h2["clk"][0] * nu.pow([14 as u64])
        + com_fh1h2["clk"][2] * nu.pow([15 as u64])
        + com_opc_table * nu.pow([16 as u64])
        + com_fh1h2["opc"][0] * nu.pow([17 as u64])
        + com_fh1h2["opc"][2] * nu.pow([18 as u64])
        + (com_w["clk"]
            + com_w["ip"] * nu
            + com_w["mp"] * nu.pow([2 as u64])
            + com_w["mv"] * nu.pow([3 as u64])
            + com_w["mem_clk"] * nu.pow([4 as u64])
            + com_w["mem_mp"] * nu.pow([5 as u64])
            + com_w["mem_mv"] * nu.pow([6 as u64])
            + com_z["out"] * nu.pow([7 as u64])
            + com_z["in"] * nu.pow([8 as u64])
            + com_z["mem"] * nu.pow([9 as u64])
            + com_z["txt"] * nu.pow([10 as u64])
            + com_z["clk"] * nu.pow([11 as u64])
            + com_z["opc"] * nu.pow([12 as u64])
            + com_prog_text * nu.pow([13 as u64])
            + com_fh1h2["txt"][1] * nu.pow([14 as u64])
            + com_clk_table * nu.pow([15 as u64])
            + com_fh1h2["clk"][1] * nu.pow([16 as u64])
            + com_opc_table * nu.pow([17 as u64])
            + com_fh1h2["opc"][1] * nu.pow([18 as u64]))
            * eta;

    // 12. Compute the group-encoded batch evaluation
    let e1 = G1::generator()
        * (-r0
            + w["clk"] * nu
            + w["ip"] * nu.pow([2 as u64])
            + w["ni"] * nu.pow([3 as u64])
            + w["mp"] * nu.pow([4 as u64])
            + w["mv"] * nu.pow([5 as u64])
            + w["mvz"] * nu.pow([6 as u64])
            + w["mem_mp"] * nu.pow([7 as u64])
            + z["out"] * nu.pow([8 as u64])
            + z["in"] * nu.pow([9 as u64])
            + ttfh1h2["txt"][0] * nu.pow([10 as u64])
            + ttfh1h2["txt"][2] * nu.pow([11 as u64])
            + ttfh1h2["txt"][4] * nu.pow([12 as u64])
            + ttfh1h2["clk"][0] * nu.pow([13 as u64])
            + ttfh1h2["clk"][2] * nu.pow([14 as u64])
            + ttfh1h2["clk"][4] * nu.pow([15 as u64])
            + ttfh1h2["opc"][0] * nu.pow([16 as u64])
            + ttfh1h2["opc"][2] * nu.pow([17 as u64])
            + ttfh1h2["opc"][4] * nu.pow([18 as u64])
            + eta
                * (w["o_clk"]
                    + w["o_ip"] * nu
                    + w["o_mp"] * nu.pow([2 as u64])
                    + w["o_mv"] * nu.pow([3 as u64])
                    + w["o_mem_clk"] * nu.pow([4 as u64])
                    + w["o_mem_mp"] * nu.pow([5 as u64])
                    + w["o_mem_mv"] * nu.pow([6 as u64])
                    + z["o_out"] * nu.pow([7 as u64])
                    + z["o_in"] * nu.pow([8 as u64])
                    + z["o_mem"] * nu.pow([9 as u64])
                    + z["o_txt"] * nu.pow([10 as u64])
                    + z["o_clk"] * nu.pow([11 as u64])
                    + z["o_opc"] * nu.pow([12 as u64])
                    + ttfh1h2["txt"][1] * nu.pow([13 as u64])
                    + ttfh1h2["txt"][3] * nu.pow([14 as u64])
                    + ttfh1h2["clk"][1] * nu.pow([15 as u64])
                    + ttfh1h2["clk"][3] * nu.pow([16 as u64])
                    + ttfh1h2["opc"][1] * nu.pow([17 as u64])
                    + ttfh1h2["opc"][3] * nu.pow([18 as u64])));

    // 13. Finally, batch validate all evaluations
    let com_bigw = commitments.w();
    let omega = ppi.cpi().domain.group_gen;

    Bls12_381::pairing(
        com_bigw["mu"] + com_bigw["omega_mu"] * eta,
        ppi.cpi().srs.elements_of_g2()[1],
    ) == Bls12_381::pairing(
        com_bigw["mu"] * mu + com_bigw["omega_mu"] * eta * mu * omega + f1 - e1,
        ppi.cpi().srs.elements_of_g2()[0],
    )
}
