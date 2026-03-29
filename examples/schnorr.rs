/// Schnorr protocol in arkΣΠ — prove knowledge of discrete log.
///
/// Proves: "I know sk such that pk = g * sk" without revealing sk.
///
/// Run: cargo run --example schnorr --release

use std::collections::HashMap;

use ark_bls12_381::{Fr, G1Projective};
use ark_ec::CurveGroup;
use ark_ff::UniformRand;
use ark_std::rand::SeedableRng;
use egg::{RecExpr, Symbol};
use rand::rngs::StdRng;
use spongefish::domain_separator;

use ark_sigma_pi::{eval_with_sponge, eval_with_verifier, ArkLang, Env, SpongeTable, Value, VerifierTable};

// ── Prover program (asumpi S-expression) ──
//
// Inputs: s (ProverState), pk (Curve), R (Curve), k (Field), sk (Field)
// Output: final ProverState (with transcript containing R, z)
const PROVER_PROGRAM: &str = "\
(let s1 (absorb_public Curve s pk) \
  (let s2 (absorb_private Curve s1 R) \
    (let r (squeeze Field s2) \
      (let c (fst r) \
        (let s3 (snd r) \
          (let z (add Field Field k (mul Field Field c sk)) \
            (absorb_private Field s3 z)))))))";

// ── Verifier program (asumpi S-expression) ──
//
// Inputs: vs (VerifierState), pk (Curve), g (Curve)
// Output: Bool(true) if proof valid, error otherwise
const VERIFIER_PROGRAM: &str = "\
(let vs1 (absorb_public Curve vs pk) \
  (let r1 (read_transcript Curve vs1) \
    (let R (fst r1) \
      (let vs2 (snd r1) \
        (let r2 (squeeze Field vs2) \
          (let c (fst r2) \
            (let vs3 (snd r2) \
              (let r3 (read_transcript Field vs3) \
                (let z (fst r3) \
                  (let vs4 (snd r3) \
                    (let _eof (check_eof vs4) \
                      (verify (eq Curve \
                        (mul Field Curve z g) \
                        (add Curve Curve R (mul Field Curve c pk)))))))))))))))";

fn main() {
    println!("=== Schnorr Protocol in arkΣΠ ===\n");

    // ── Setup ──
    let mut rng = StdRng::seed_from_u64(42);
    let g = G1Projective::rand(&mut rng);
    let sk = Fr::rand(&mut rng);
    let pk = g * sk;
    let k = Fr::rand(&mut rng); // random nonce
    let commitment = g * k; // R = g * k

    println!("Generator:  {}", g.into_affine());
    println!("Public key: {}", pk.into_affine());
    println!("Commitment: {}", commitment.into_affine());

    // ── Domain separator (shared between prover and verifier) ──
    let domsep = domain_separator!("schnorr-proof-of-knowledge"; "asumpi-examples")
        .instance(&0u32);

    // ── Run Prover ──
    println!("\n── Prover ──");
    let st = SpongeTable::new();
    let prover = domsep.std_prover();
    let prover_id = st.insert(prover);

    let mut prover_env: Env = HashMap::new();
    prover_env.insert(Symbol::from("s"), Value::ProverState(prover_id));
    prover_env.insert(Symbol::from("pk"), Value::Curve(pk));
    prover_env.insert(Symbol::from("R"), Value::Curve(commitment));
    prover_env.insert(Symbol::from("k"), Value::Field(k));
    prover_env.insert(Symbol::from("sk"), Value::Field(sk));

    let prover_expr: RecExpr<ArkLang> = PROVER_PROGRAM.parse().expect("prover parse failed");
    let prover_result = eval_with_sponge(&prover_expr, &prover_env, &st)
        .expect("prover evaluation failed");

    // Extract transcript from final prover state
    let final_id = match &prover_result {
        Value::ProverState(id) => *id,
        _ => panic!("expected ProverState, got {:?}", prover_result),
    };
    let final_prover = st.take(final_id).expect("prover state already consumed");
    let transcript = final_prover.narg_string().to_vec();

    println!("Transcript length: {} bytes", transcript.len());
    println!("Transcript (hex):  {}", transcript.iter().map(|b| format!("{:02x}", b)).collect::<String>());

    // ── Run Verifier ──
    println!("\n── Verifier ──");
    let vt = VerifierTable::new();
    let vid = vt.insert_with(transcript, |t| domsep.std_verifier(t));

    let mut verifier_env: Env = HashMap::new();
    verifier_env.insert(Symbol::from("vs"), Value::VerifierState(vid));
    verifier_env.insert(Symbol::from("pk"), Value::Curve(pk));
    verifier_env.insert(Symbol::from("g"), Value::Curve(g));

    let verifier_expr: RecExpr<ArkLang> = VERIFIER_PROGRAM.parse().expect("verifier parse failed");
    match eval_with_verifier(&verifier_expr, &verifier_env, &vt) {
        Ok(Value::Bool(true)) => println!("✅ Schnorr proof VERIFIED"),
        Ok(other) => println!("❌ Unexpected result: {:?}", other),
        Err(e) => println!("❌ Verification FAILED: {}", e),
    }

    println!("\n=== Done ===");
}
