// Algebraic Law Property Tests for arkΣΠ
//
// Verifies that every rewrite rule preserves evaluation semantics,
// the optimizer round-trip is correct, and guards are necessary.

mod common;

use ark_ff::Zero;
use ark_sigma_pi::*;
use egg::{AstSize, Extractor, RecExpr, Runner};
use proptest::prelude::*;
use std::collections::HashMap;

use common::{fr, eval_str, env_with_fields};

/// Run egg optimizer with all rules, extract best, evaluate.
fn optimize_and_eval(expr_str: &str, env: &Env) -> Value {
    let expr: RecExpr<ArkLang> = expr_str.parse().unwrap();
    let runner: Runner<ArkLang, TypeAnalysis> = Runner::default()
        .with_expr(&expr)
        .run(&all_rules());
    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_, best) = extractor.find_best(root);
    eval(&best, env).expect("eval of optimized expr failed")
}

// ═══════════════════════════════════════════════════════════════════
// Phase 1a — Algebra Rule Soundness
// ═══════════════════════════════════════════════════════════════════

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    // Rule: (scale 1 a) => a
    #[test]
    fn rule_scale_one_field(a_val in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a_val))]);
        let lhs = eval_str("(tscale Field 1 a)", &env).as_field().unwrap();
        let rhs = eval_str("a", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (scale 1 p) => p — polynomial version via eval
    #[test]
    fn rule_scale_one_poly(c0 in any::<u64>(), c1 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1)), ("x", fr(x))]);
        let lhs = eval_str("(eval (tscale DensePoly 1 (poly:duv c0 c1)) x)", &env).as_field().unwrap();
        let rhs = eval_str("(eval (poly:duv c0 c1) x)", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (scale 0 a) => 0
    #[test]
    fn rule_scale_zero_field(a_val in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a_val))]);
        let lhs = eval_str("(tscale Field 0 a)", &env).as_field().unwrap();
        prop_assert!(lhs.is_zero());
    }

    // Rule: (add a (neg a)) => 0
    #[test]
    fn rule_add_neg_field(a_val in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a_val))]);
        let lhs = eval_str("(add a (tneg Field a))", &env).as_field().unwrap();
        prop_assert!(lhs.is_zero());
    }

    // Rule: (neg a) => (scale -1 a)
    #[test]
    fn rule_neg_as_scale_field(a_val in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a_val))]);
        let lhs = eval_str("(tneg Field a)", &env).as_field().unwrap();
        let rhs = eval_str("(tscale Field -1 a)", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (neg p) => (scale -1 p) — polynomial version via eval
    #[test]
    fn rule_neg_as_scale_poly(c0 in any::<u64>(), c1 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1)), ("x", fr(x))]);
        let lhs = eval_str("(eval (tneg DensePoly (poly:duv c0 c1)) x)", &env).as_field().unwrap();
        let rhs = eval_str("(eval (tscale DensePoly -1 (poly:duv c0 c1)) x)", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }
}

// ═══════════════════════════════════════════════════════════════════
// Phase 1b — Eval Distribution Soundness
// ═══════════════════════════════════════════════════════════════════

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    // Rule: (eval (add p q) x) => (add (eval p x) (eval q x))
    #[test]
    fn rule_eval_add(
        a0 in any::<u64>(), a1 in any::<u64>(),
        b0 in any::<u64>(), b1 in any::<u64>(),
        x in any::<u64>()
    ) {
        let env = env_with_fields(&[
            ("a0", fr(a0)), ("a1", fr(a1)),
            ("b0", fr(b0)), ("b1", fr(b1)),
            ("x", fr(x)),
        ]);
        let lhs = eval_str("(eval (add (poly:duv a0 a1) (poly:duv b0 b1)) x)", &env).as_field().unwrap();
        let rhs = eval_str("(add (eval (poly:duv a0 a1) x) (eval (poly:duv b0 b1) x))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (eval (neg p) x) => (neg (eval p x))
    #[test]
    fn rule_eval_neg(c0 in any::<u64>(), c1 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1)), ("x", fr(x))]);
        let lhs = eval_str("(eval (tneg DensePoly (poly:duv c0 c1)) x)", &env).as_field().unwrap();
        let rhs = eval_str("(tneg Field (eval (poly:duv c0 c1) x))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (eval (scale c p) x) => (mul c (eval p x))
    #[test]
    fn rule_eval_scale(c in any::<u64>(), c0 in any::<u64>(), c1 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c", fr(c)), ("c0", fr(c0)), ("c1", fr(c1)), ("x", fr(x))]);
        let lhs = eval_str("(eval (tscale DensePoly c (poly:duv c0 c1)) x)", &env).as_field().unwrap();
        let rhs = eval_str("(mul c (eval (poly:duv c0 c1) x))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (eval (mul p q) x) => (mul (eval p x) (eval q x))
    #[test]
    fn rule_eval_mul(
        a0 in any::<u64>(), a1 in any::<u64>(),
        b0 in any::<u64>(), b1 in any::<u64>(),
        x in any::<u64>()
    ) {
        let env = env_with_fields(&[
            ("a0", fr(a0)), ("a1", fr(a1)),
            ("b0", fr(b0)), ("b1", fr(b1)),
            ("x", fr(x)),
        ]);
        let lhs = eval_str("(eval (mul (poly:duv a0 a1) (poly:duv b0 b1)) x)", &env).as_field().unwrap();
        let rhs = eval_str("(mul (eval (poly:duv a0 a1) x) (eval (poly:duv b0 b1) x))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }
}

// ═══════════════════════════════════════════════════════════════════
// Phase 1c — Σ/Π Unrolling Soundness
// ═══════════════════════════════════════════════════════════════════

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    // Rule: (Σ i 0 1 f) => (let i 0 f)
    #[test]
    fn rule_sigma_unroll_1(a in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a))]);
        let lhs = eval_str("(Σ i 0 1 (tselect Field (mkarray a) i))", &env).as_field().unwrap();
        let rhs = eval_str("(let i 0 (tselect Field (mkarray a) i))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (Σ i 0 2 f) => (add (let i 0 f) (let i 1 f))
    #[test]
    fn rule_sigma_unroll_2(a in any::<u64>(), b in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b))]);
        let lhs = eval_str("(Σ i 0 2 (tselect Field (mkarray a b) i))", &env).as_field().unwrap();
        let rhs = eval_str("(add (let i 0 (tselect Field (mkarray a b) i)) (let i 1 (tselect Field (mkarray a b) i)))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (Σ i 0 3 f) => (add (let i 0 f) (add (let i 1 f) (let i 2 f)))
    #[test]
    fn rule_sigma_unroll_3(a in any::<u64>(), b in any::<u64>(), c in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b)), ("c", fr(c))]);
        let lhs = eval_str("(Σ i 0 3 (tselect Field (mkarray a b c) i))", &env).as_field().unwrap();
        let rhs = eval_str(
            "(add (let i 0 (tselect Field (mkarray a b c) i)) \
                  (add (let i 1 (tselect Field (mkarray a b c) i)) \
                       (let i 2 (tselect Field (mkarray a b c) i))))",
            &env,
        ).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (Σ i lo hi (add f g)) => (add (Σ i lo hi f) (Σ i lo hi g))
    #[test]
    fn rule_sigma_dist_add(a in any::<u64>(), b in any::<u64>(), c in any::<u64>(), d in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b)), ("c", fr(c)), ("d", fr(d))]);
        let lhs = eval_str(
            "(Σ i 0 2 (add (tselect Field (mkarray a b) i) (tselect Field (mkarray c d) i)))",
            &env,
        ).as_field().unwrap();
        let rhs = eval_str(
            "(add (Σ i 0 2 (tselect Field (mkarray a b) i)) (Σ i 0 2 (tselect Field (mkarray c d) i)))",
            &env,
        ).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (Π i 0 1 f) => (let i 0 f)
    #[test]
    fn rule_pi_unroll_1(a in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a))]);
        let lhs = eval_str("(Π i 0 1 (tselect Field (mkarray a) i))", &env).as_field().unwrap();
        let rhs = eval_str("(let i 0 (tselect Field (mkarray a) i))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: (Π i 0 2 f) => (mul (let i 0 f) (let i 1 f))
    #[test]
    fn rule_pi_unroll_2(a in any::<u64>(), b in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b))]);
        let lhs = eval_str("(Π i 0 2 (tselect Field (mkarray a b) i))", &env).as_field().unwrap();
        let rhs = eval_str("(mul (let i 0 (tselect Field (mkarray a b) i)) (let i 1 (tselect Field (mkarray a b) i)))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }
}

// ═══════════════════════════════════════════════════════════════════
// Phase 1d — Guarded Σ Rule Soundness
// ═══════════════════════════════════════════════════════════════════

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    // Rule: Σ(scale(c, f(i))) ≡ scale(c, Σ(f(i))) when c independent of i
    #[test]
    fn rule_sigma_factor_scale(c in any::<u64>(), a in any::<u64>(), b in any::<u64>(), d in any::<u64>()) {
        let env = env_with_fields(&[("c", fr(c)), ("a", fr(a)), ("b", fr(b)), ("d", fr(d))]);
        let lhs = eval_str(
            "(Σ i 0 3 (tscale Field c (tselect Field (mkarray a b d) i)))",
            &env,
        ).as_field().unwrap();
        let rhs = eval_str(
            "(tscale Field c (Σ i 0 3 (tselect Field (mkarray a b d) i)))",
            &env,
        ).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: Σ(mul(c, f(i))) ≡ mul(c, Σ(f(i))) when c independent of i
    #[test]
    fn rule_sigma_factor_mul(c in any::<u64>(), a in any::<u64>(), b in any::<u64>()) {
        let env = env_with_fields(&[("c", fr(c)), ("a", fr(a)), ("b", fr(b))]);
        let lhs = eval_str(
            "(Σ i 0 2 (mul c (tselect Field (mkarray a b) i)))",
            &env,
        ).as_field().unwrap();
        let rhs = eval_str(
            "(mul c (Σ i 0 2 (tselect Field (mkarray a b) i)))",
            &env,
        ).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: Σ f + Σ g ≡ Σ(f + g) — same range (sigma-fusion)
    #[test]
    fn rule_sigma_fusion(a in any::<u64>(), b in any::<u64>(), c in any::<u64>(), d in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b)), ("c", fr(c)), ("d", fr(d))]);
        let lhs = eval_str(
            "(add (Σ i 0 2 (tselect Field (mkarray a b) i)) (Σ i 0 2 (tselect Field (mkarray c d) i)))",
            &env,
        ).as_field().unwrap();
        let rhs = eval_str(
            "(Σ i 0 2 (add (tselect Field (mkarray a b) i) (tselect Field (mkarray c d) i)))",
            &env,
        ).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }
}

// ═══════════════════════════════════════════════════════════════════
// Phase 1e — Conversion Roundtrip Soundness
// ═══════════════════════════════════════════════════════════════════

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    // Rule: densify(sparsify(p)) ≡ p
    #[test]
    fn rule_densify_sparsify(c0 in any::<u64>(), c1 in any::<u64>(), c2 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1)), ("c2", fr(c2)), ("x", fr(x))]);
        let lhs = eval_str("(eval (coerce SparsePoly DensePoly (coerce DensePoly SparsePoly (poly:duv c0 c1 c2))) x)", &env).as_field().unwrap();
        let rhs = eval_str("(eval (poly:duv c0 c1 c2) x)", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: sparsify(densify(p)) ≡ p — start from sparse
    #[test]
    fn rule_sparsify_densify(c0 in any::<u64>(), c2 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c2", fr(c2)), ("x", fr(x))]);
        // poly:suv with term (0, c0) and (2, c2)
        let lhs = eval_str("(eval (coerce DensePoly SparsePoly (coerce SparsePoly DensePoly (poly:suv 0 c0 2 c2))) x)", &env).as_field().unwrap();
        let rhs = eval_str("(eval (poly:suv 0 c0 2 c2) x)", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: as-uv(as-mle(p)) ≡ p — for 1-var UV poly (linear)
    #[test]
    fn rule_as_uv_as_mle(c0 in any::<u64>(), c1 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1)), ("x", fr(x))]);
        let lhs = eval_str("(eval (coerce DenseMLE DensePoly (coerce DensePoly DenseMLE (poly:duv c0 c1))) x)", &env).as_field().unwrap();
        let rhs = eval_str("(eval (poly:duv c0 c1) x)", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Rule: as-mle(as-uv(m)) ≡ m — for 1-var MLE
    #[test]
    fn rule_as_mle_as_uv(v0 in any::<u64>(), v1 in any::<u64>()) {
        let env = env_with_fields(&[("v0", fr(v0)), ("v1", fr(v1))]);
        // Evaluate MLE at (0) and (1) — should recover original values
        let lhs_0 = eval_str(
            "(eval (coerce DensePoly DenseMLE (coerce DenseMLE DensePoly (poly:dmle 1 (mkarray v0 v1)))) (mkarray 0))",
            &env,
        ).as_field().unwrap();
        let rhs_0 = eval_str("(eval (poly:dmle 1 (mkarray v0 v1)) (mkarray 0))", &env).as_field().unwrap();
        prop_assert_eq!(lhs_0, rhs_0);

        let lhs_1 = eval_str(
            "(eval (coerce DensePoly DenseMLE (coerce DenseMLE DensePoly (poly:dmle 1 (mkarray v0 v1)))) (mkarray 1))",
            &env,
        ).as_field().unwrap();
        let rhs_1 = eval_str("(eval (poly:dmle 1 (mkarray v0 v1)) (mkarray 1))", &env).as_field().unwrap();
        prop_assert_eq!(lhs_1, rhs_1);
    }
}

// ═══════════════════════════════════════════════════════════════════
// Phase 2 — Optimizer Round-Trip (Compiler Correctness)
// ═══════════════════════════════════════════════════════════════════

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    // eval(optimize(field_expr)) == eval(field_expr)
    #[test]
    fn optimizer_roundtrip_field_arith(a in any::<u64>(), b in any::<u64>(), c in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b)), ("c", fr(c))]);
        // Expression that multiple rules can transform:
        // scale(c, add(a, b)) can be distributed, reordered, etc.
        let expr = "(add (tscale Field c (add a b)) (tneg Field (mul a b)))";
        let original = eval_str(expr, &env);
        let optimized = optimize_and_eval(expr, &env);
        prop_assert_eq!(original, optimized);
    }

    // eval(optimize(poly_eval_chain)) == eval(poly_eval_chain)
    #[test]
    fn optimizer_roundtrip_poly_eval(
        a0 in any::<u64>(), a1 in any::<u64>(),
        b0 in any::<u64>(), b1 in any::<u64>(),
        c in any::<u64>(), x in any::<u64>()
    ) {
        let env = env_with_fields(&[
            ("a0", fr(a0)), ("a1", fr(a1)),
            ("b0", fr(b0)), ("b1", fr(b1)),
            ("c", fr(c)), ("x", fr(x)),
        ]);
        // eval(scale(c, add(p, q)), x) — multiple rules apply
        let expr = "(eval (tscale DensePoly c (add (poly:duv a0 a1) (poly:duv b0 b1))) x)";
        let original = eval_str(expr, &env);
        let optimized = optimize_and_eval(expr, &env);
        prop_assert_eq!(original, optimized);
    }

    // eval(optimize(sigma_msm)) == eval(sigma_msm)
    #[test]
    fn optimizer_roundtrip_sigma_msm(a in any::<u64>(), b in any::<u64>(), c in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b)), ("c", fr(c))]);
        // Σ distributes, can unroll, etc.
        let expr = "(Σ i 0 3 (tselect Field (mkarray a b c) i))";
        let original = eval_str(expr, &env);
        let optimized = optimize_and_eval(expr, &env);
        prop_assert_eq!(original, optimized);
    }

    // Mixed: poly eval + sigma + scale
    #[test]
    fn optimizer_roundtrip_mixed(a in any::<u64>(), b in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b)), ("x", fr(x))]);
        let expr = "(add (eval (poly:duv a b) x) (Σ i 0 2 (tselect Field (mkarray a b) i)))";
        let original = eval_str(expr, &env);
        let optimized = optimize_and_eval(expr, &env);
        prop_assert_eq!(original, optimized);
    }
}

// ═══════════════════════════════════════════════════════════════════
// Phase 3 — Guard Necessity (counterexamples)
// ═══════════════════════════════════════════════════════════════════

#[test]
fn guard_necessity_sigma_factor_scale() {
    // Without the IndependentOf guard, factoring (scale i ...) out of Σ is wrong.
    // Σ i=0..3 scale(i, a_i) ≠ scale(i, Σ i=0..3 a_i)  (RHS uses i as a free var)
    //
    // LHS: 0*10 + 1*20 + 2*30 = 0 + 20 + 60 = 80
    // RHS: if i=0 in env, scale(0, 10+20+30) = 0. Wrong!
    // RHS: if i=1 in env, scale(1, 60) = 60. Still wrong!
    let env: Env = HashMap::new();
    let lhs = eval_str(
        "(Σ i 0 3 (mul i (tselect Int (mkarray 10 20 30) i)))",
        &env,
    ).as_field().unwrap();
    assert_eq!(lhs, fr(80)); // 0*10 + 1*20 + 2*30

    // The "incorrectly factored" form uses a concrete i=0 in env (unbound → error),
    // proving the rewrite can't be applied when c depends on i.
    // Instead, we demonstrate the factored form evaluates differently for any fixed i:
    let mut env_i0: Env = HashMap::new();
    env_i0.insert("i".into(), Value::Int(0));
    let rhs_i0 = eval_str(
        "(mul i (Σ i 0 3 (tselect Int (mkarray 10 20 30) i)))",
        &env_i0,
    ).as_field().unwrap();
    // rhs_i0 = 0 * (10+20+30) = 0 ≠ 80
    assert_ne!(lhs, rhs_i0, "Factoring scale(i,...) out of Σ over i is unsound");
}

#[test]
fn guard_necessity_sigma_factor_mul() {
    // Σ i=0..2 mul(i, a_i) ≠ mul(i, Σ a_i) for any fixed i
    let env: Env = HashMap::new();
    let lhs = eval_str(
        "(Σ i 0 2 (mul i (tselect Int (mkarray 10 20) i)))",
        &env,
    ).as_field().unwrap();
    assert_eq!(lhs, fr(20)); // 0*10 + 1*20

    let mut env_i1: Env = HashMap::new();
    env_i1.insert("i".into(), Value::Int(1));
    let rhs_i1 = eval_str(
        "(mul i (Σ i 0 2 (tselect Int (mkarray 10 20) i)))",
        &env_i1,
    ).as_field().unwrap();
    // rhs = 1 * (10+20) = 30 ≠ 20
    assert_ne!(lhs, rhs_i1, "Factoring mul(i,...) out of Σ over i is unsound");
}

// ═══════════════════════════════════════════════════════════════════
// Phase 4 — Cross-Type & Edge-Case Laws
// ═══════════════════════════════════════════════════════════════════

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    // scale(a, scale(b, P)) == scale(a*b, P)
    #[test]
    fn scale_associativity(a in any::<u64>(), b in any::<u64>(), p in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b)), ("p", fr(p))]);
        let lhs = eval_str("(tscale Field a (tscale Field b p))", &env).as_field().unwrap();
        let rhs = eval_str("(tscale Field (mul a b) p)", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // pow(a, m) * pow(a, n) == pow(a, m+n)
    #[test]
    fn pow_additive(a_val in 1u64..1000, m in 0i64..5, n in 0i64..5) {
        let env = env_with_fields(&[("a", fr(a_val))]);
        let lhs_expr = format!("(mul (tpow Field a {}) (tpow Field a {}))", m, n);
        let rhs_expr = format!("(tpow Field a {})", m + n);
        let lhs = eval_str(&lhs_expr, &env).as_field().unwrap();
        let rhs = eval_str(&rhs_expr, &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Σ(i, N, N, f) == Int(0) (empty range produces additive identity)
    #[test]
    fn sigma_empty_range(n in 0i64..10) {
        let env: Env = HashMap::new();
        let expr = format!("(Σ i {} {} (mul i i))", n, n);
        let r = eval_str(&expr, &env);
        prop_assert_eq!(r, Value::Int(0));
    }

    // Π(i, N, N, f) == Int(1) (empty range produces multiplicative identity)
    #[test]
    fn pi_empty_range(n in 0i64..10) {
        let env: Env = HashMap::new();
        let expr = format!("(Π i {} {} (mul i i))", n, n);
        let r = eval_str(&expr, &env);
        prop_assert_eq!(r, Value::Int(1));
    }

    // Σ(i, N, N+1, f) == let(i, N, f)
    #[test]
    fn sigma_single_elem(n in 0i64..5, a in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a))]);
        let lhs = format!("(Σ i {n} {} (add a i))", n + 1);
        let rhs = format!("(let i {n} (add a i))");
        let l = eval_str(&lhs, &env);
        let r = eval_str(&rhs, &env);
        prop_assert_eq!(l, r);
    }

    // (let x v (add x x)) == (add v v)
    #[test]
    fn let_is_substitution(v in any::<u64>()) {
        let env = env_with_fields(&[("v", fr(v))]);
        let lhs = eval_str("(let x v (add x x))", &env).as_field().unwrap();
        let rhs = eval_str("(add v v)", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // eval(densify(sparsify(p)), x) == eval(p, x) — conversion preserves poly eval
    #[test]
    fn conversion_preserves_eval(c0 in any::<u64>(), c1 in any::<u64>(), c2 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1)), ("c2", fr(c2)), ("x", fr(x))]);
        let lhs = eval_str("(eval (coerce SparsePoly DensePoly (coerce DensePoly SparsePoly (poly:duv c0 c1 c2))) x)", &env).as_field().unwrap();
        let rhs = eval_str("(eval (poly:duv c0 c1 c2) x)", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // ifft(n, fft(n, p)) preserves polynomial evaluation
    #[test]
    fn fft_ifft_roundtrip(c0 in any::<u64>(), c1 in any::<u64>(), c2 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1)), ("c2", fr(c2)), ("x", fr(x))]);
        let original = eval_str("(eval (poly:duv c0 c1 c2) x)", &env).as_field().unwrap();
        let roundtripped = eval_str("(eval (tifft Array 4 (tfft DensePoly 4 (poly:duv c0 c1 c2))) x)", &env).as_field().unwrap();
        prop_assert_eq!(original, roundtripped);
    }

    // fft evaluations match pointwise polynomial evaluation at domain elements
    #[test]
    fn fft_matches_point_eval(c0 in any::<u64>(), c1 in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1))]);
        // FFT of linear poly c0 + c1*x at domain size 4
        let evals = eval_str("(tfft DensePoly 4 (poly:duv c0 c1))", &env).as_array().unwrap();
        let domain_pts = eval_str("(domain 4)", &env).as_array().unwrap();
        for i in 0..4 {
            let omega_i = domain_pts[i].as_field().unwrap();
            let expected = fr(c0) + fr(c1) * omega_i;
            prop_assert_eq!(evals[i].as_field().unwrap(), expected);
        }
    }

    // optimizer roundtrip: optimize(ifft(n, fft(n, p))) evals same as p
    #[test]
    fn optimizer_fft_roundtrip(c0 in any::<u64>(), c1 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1)), ("x", fr(x))]);
        let original = eval_str("(eval (poly:duv c0 c1) x)", &env).as_field().unwrap();
        let optimized = optimize_and_eval("(eval (tifft Array 4 (tfft DensePoly 4 (poly:duv c0 c1))) x)", &env).as_field().unwrap();
        prop_assert_eq!(original, optimized);
    }

    // pdiv division identity: a = q*b + r at all points
    #[test]
    fn pdiv_division_identity(c0 in any::<u64>(), c1 in any::<u64>(), c2 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1)), ("c2", fr(c2)), ("x", fr(x))]);
        let a = eval_str("(eval (poly:duv c0 c1 c2) x)", &env).as_field().unwrap();
        let q = eval_str("(eval (fst (tpdiv DensePoly (poly:duv c0 c1 c2) (poly:duv 1 1))) x)", &env).as_field().unwrap();
        let b = eval_str("(eval (poly:duv 1 1) x)", &env).as_field().unwrap();
        let r = eval_str("(eval (snd (tpdiv DensePoly (poly:duv c0 c1 c2) (poly:duv 1 1))) x)", &env).as_field().unwrap();
        prop_assert_eq!(a, q * b + r);
    }

    // aadd commutativity
    #[test]
    fn aadd_commutative(a0 in any::<u64>(), a1 in any::<u64>(), b0 in any::<u64>(), b1 in any::<u64>(), b2 in any::<u64>()) {
        let env = env_with_fields(&[("a0", fr(a0)), ("a1", fr(a1)), ("b0", fr(b0)), ("b1", fr(b1)), ("b2", fr(b2))]);
        let lhs = eval_str("(taadd Field (mkarray a0 a1) (mkarray b0 b1 b2))", &env).as_array().unwrap();
        let rhs = eval_str("(taadd Field (mkarray b0 b1 b2) (mkarray a0 a1))", &env).as_array().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // fst/snd projection on pair
    #[test]
    fn pair_projection(a in any::<u64>(), b in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b))]);
        let fst = eval_str("(fst (pair a b))", &env).as_field().unwrap();
        let snd = eval_str("(snd (pair a b))", &env).as_field().unwrap();
        prop_assert_eq!(fst, fr(a));
        prop_assert_eq!(snd, fr(b));
    }

    // optimizer roundtrip: fst(pair(a,b)) optimizes to a
    #[test]
    fn optimizer_pair_roundtrip(a in any::<u64>(), b in any::<u64>()) {
        let env = env_with_fields(&[("a", fr(a)), ("b", fr(b))]);
        let original = eval_str("a", &env).as_field().unwrap();
        let optimized = optimize_and_eval("(fst (pair a b))", &env).as_field().unwrap();
        prop_assert_eq!(original, optimized);
    }

    // optimizer roundtrip: densify(sparsify(p)) optimizes to p (eval at point)
    #[test]
    fn optimizer_conversion_roundtrip(c0 in any::<u64>(), c1 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[("c0", fr(c0)), ("c1", fr(c1)), ("x", fr(x))]);
        let original = eval_str("(eval (poly:duv c0 c1) x)", &env).as_field().unwrap();
        let optimized = optimize_and_eval("(eval (coerce SparsePoly DensePoly (coerce DensePoly SparsePoly (poly:duv c0 c1))) x)", &env).as_field().unwrap();
        prop_assert_eq!(original, optimized);
    }
}
