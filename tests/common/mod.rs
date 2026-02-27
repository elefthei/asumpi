// Shared test helpers for arkΣΠ integration tests.

use ark_bls12_381::Fr;
use ark_wasm_lang::{eval, ArkLang, Env, Value};
use egg::RecExpr;
use std::collections::HashMap;

pub fn fr(n: u64) -> Fr {
    Fr::from(n)
}

pub fn eval_str(s: &str, env: &Env) -> Value {
    let expr: RecExpr<ArkLang> = s.parse().expect("parse failed");
    eval(&expr, env).expect("eval failed")
}

pub fn env_with_fields(vals: &[(&str, Fr)]) -> Env {
    let mut env = HashMap::new();
    for (name, val) in vals {
        env.insert((*name).into(), Value::Field(*val));
    }
    env
}
