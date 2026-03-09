// Property-based tests for arkΣΠ language.
// Verifies algebraic identities hold for random inputs.

mod common;

use ark_bls12_381::{Fr, G1Projective};
use ark_ec::CurveGroup;
use ark_ff::{UniformRand, Zero};
use ark_std::rand::SeedableRng;
use ark_sigma_pi::{Env, Value};
use proptest::prelude::*;
use rand::rngs::StdRng;
use std::collections::HashMap;

use common::{fr as fr_from_u64, eval_str, env_with_fields};

// ── Field Property Tests ──

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn field_add_commutative(a_val in any::<u64>(), b_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let b = fr_from_u64(b_val);
        let env = env_with_fields(&[("a", a), ("b", b)]);

        let r1 = eval_str("(tadd Field Field a b)", &env).as_field().unwrap();
        let r2 = eval_str("(tadd Field Field b a)", &env).as_field().unwrap();
        prop_assert_eq!(r1, r2);
    }

    #[test]
    fn field_mul_commutative(a_val in any::<u64>(), b_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let b = fr_from_u64(b_val);
        let env = env_with_fields(&[("a", a), ("b", b)]);

        let r1 = eval_str("(tmul Field Field a b)", &env).as_field().unwrap();
        let r2 = eval_str("(tmul Field Field b a)", &env).as_field().unwrap();
        prop_assert_eq!(r1, r2);
    }

    #[test]
    fn field_add_associative(a_val in any::<u64>(), b_val in any::<u64>(), c_val in any::<u64>()) {
        let (a, b, c) = (fr_from_u64(a_val), fr_from_u64(b_val), fr_from_u64(c_val));
        let env = env_with_fields(&[("a", a), ("b", b), ("c", c)]);

        let lhs = eval_str("(tadd Field Field (tadd Field Field a b) c)", &env).as_field().unwrap();
        let rhs = eval_str("(tadd Field Field a (tadd Field Field b c))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[test]
    fn field_mul_associative(a_val in any::<u64>(), b_val in any::<u64>(), c_val in any::<u64>()) {
        let (a, b, c) = (fr_from_u64(a_val), fr_from_u64(b_val), fr_from_u64(c_val));
        let env = env_with_fields(&[("a", a), ("b", b), ("c", c)]);

        let lhs = eval_str("(tmul Field Field (tmul Field Field a b) c)", &env).as_field().unwrap();
        let rhs = eval_str("(tmul Field Field a (tmul Field Field b c))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[test]
    fn field_distributive(a_val in any::<u64>(), b_val in any::<u64>(), c_val in any::<u64>()) {
        let (a, b, c) = (fr_from_u64(a_val), fr_from_u64(b_val), fr_from_u64(c_val));
        let env = env_with_fields(&[("a", a), ("b", b), ("c", c)]);

        let lhs = eval_str("(tmul Field Field a (tadd Field Field b c))", &env).as_field().unwrap();
        let rhs = eval_str("(tadd Field Field (tmul Field Field a b) (tmul Field Field a c))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[test]
    fn field_additive_identity(a_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(tadd Field Field a 0)", &env).as_field().unwrap();
        prop_assert_eq!(r, a);
    }

    #[test]
    fn field_multiplicative_identity(a_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(tmul Field Field a 1)", &env).as_field().unwrap();
        prop_assert_eq!(r, a);
    }

    #[test]
    fn field_additive_inverse(a_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(tadd Field Field a (tneg Field a))", &env).as_field().unwrap();
        prop_assert!(r.is_zero());
    }

    #[test]
    fn field_multiplicative_inverse(a_val in 1u64..u64::MAX) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(tmul Field Field a (tinv Field a))", &env).as_field().unwrap();
        prop_assert_eq!(r, Fr::from(1u64));
    }

    #[test]
    fn field_double_negation(a_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(tneg Field (tneg Field a))", &env).as_field().unwrap();
        prop_assert_eq!(r, a);
    }

    #[test]
    fn field_sub_is_add_neg(a_val in any::<u64>(), b_val in any::<u64>()) {
        let (a, b) = (fr_from_u64(a_val), fr_from_u64(b_val));
        let env = env_with_fields(&[("a", a), ("b", b)]);

        // a - b = a + (-b)
        let r = eval_str("(tadd Field Field a (tneg Field b))", &env).as_field().unwrap();
        prop_assert_eq!(r, a - b);
    }

    #[test]
    fn field_mul_by_zero(a_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(tmul Field Field a 0)", &env).as_field().unwrap();
        prop_assert!(r.is_zero());
    }
}

// ── Curve Property Tests ──

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn curve_add_commutative(seed in any::<u64>()) {
        let mut rng = StdRng::seed_from_u64(seed);
        let p = G1Projective::rand(&mut rng);
        let q = G1Projective::rand(&mut rng);

        let mut env: Env = HashMap::new();
        env.insert("p".into(), Value::Curve(p));
        env.insert("q".into(), Value::Curve(q));

        let r1 = eval_str("(tadd Curve Curve p q)", &env).as_curve().unwrap();
        let r2 = eval_str("(tadd Curve Curve q p)", &env).as_curve().unwrap();
        prop_assert_eq!(r1.into_affine(), r2.into_affine());
    }

    #[test]
    fn curve_additive_inverse(seed in any::<u64>()) {
        let mut rng = StdRng::seed_from_u64(seed);
        let p = G1Projective::rand(&mut rng);

        let mut env: Env = HashMap::new();
        env.insert("p".into(), Value::Curve(p));

        let r = eval_str("(tadd Curve Curve p (tneg Curve p))", &env).as_curve().unwrap();
        prop_assert!(r.is_zero());
    }

    #[test]
    fn scalar_mul_linearity_sum(seed in any::<u64>(), s_val in any::<u64>()) {
        let mut rng = StdRng::seed_from_u64(seed);
        let p = G1Projective::rand(&mut rng);
        let q = G1Projective::rand(&mut rng);
        let s = fr_from_u64(s_val);

        let mut env: Env = HashMap::new();
        env.insert("p".into(), Value::Curve(p));
        env.insert("q".into(), Value::Curve(q));
        env.insert("s".into(), Value::Field(s));

        // s*(P+Q) = s*P + s*Q
        let lhs = eval_str("(tscale Curve s (tadd Curve Curve p q))", &env).as_curve().unwrap();
        let rhs = eval_str("(tadd Curve Curve (tscale Curve s p) (tscale Curve s q))", &env).as_curve().unwrap();
        prop_assert_eq!(lhs.into_affine(), rhs.into_affine());
    }

    #[test]
    fn scalar_mul_distributive(seed in any::<u64>(), a_val in any::<u64>(), b_val in any::<u64>()) {
        let mut rng = StdRng::seed_from_u64(seed);
        let p = G1Projective::rand(&mut rng);
        let a = fr_from_u64(a_val);
        let b = fr_from_u64(b_val);

        let mut env: Env = HashMap::new();
        env.insert("p".into(), Value::Curve(p));
        env.insert("a".into(), Value::Field(a));
        env.insert("b".into(), Value::Field(b));

        // (a+b)*P = a*P + b*P
        let lhs = eval_str("(tscale Curve (tadd Field Field a b) p)", &env).as_curve().unwrap();
        let rhs = eval_str("(tadd Curve Curve (tscale Curve a p) (tscale Curve b p))", &env).as_curve().unwrap();
        prop_assert_eq!(lhs.into_affine(), rhs.into_affine());
    }

    #[test]
    fn sigma_msm_linearity(seed in any::<u64>(), a_val in any::<u64>(), b_val in any::<u64>()) {
        let mut rng = StdRng::seed_from_u64(seed);
        let p = G1Projective::rand(&mut rng);
        let q = G1Projective::rand(&mut rng);
        let a = fr_from_u64(a_val);
        let b = fr_from_u64(b_val);

        let mut env: Env = HashMap::new();
        env.insert("a".into(), Value::Field(a));
        env.insert("b".into(), Value::Field(b));
        env.insert("p".into(), Value::Curve(p));
        env.insert("q".into(), Value::Curve(q));

        // Σ i=0..2 scale(s_i, P_i) == a*P + b*Q
        let sigma_r = eval_str(
            "(Σ i 0 2 (tscale Curve (tselect Field (mkarray a b) i) (tselect Curve (mkarray p q) i)))",
            &env,
        ).as_curve().unwrap();
        let manual_r = eval_str("(tadd Curve Curve (tscale Curve a p) (tscale Curve b q))", &env).as_curve().unwrap();
        prop_assert_eq!(sigma_r.into_affine(), manual_r.into_affine());
    }
}

// ── Polynomial Property Tests ──

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn poly_eval_matches_horner(
        c0 in any::<u64>(), c1 in any::<u64>(), c2 in any::<u64>(),
        x_val in any::<u64>()
    ) {
        let (fc0, fc1, fc2, fx) = (
            fr_from_u64(c0), fr_from_u64(c1), fr_from_u64(c2), fr_from_u64(x_val)
        );
        let env = env_with_fields(&[("c0", fc0), ("c1", fc1), ("c2", fc2), ("x", fx)]);

        let poly_r = eval_str("(teval DensePoly (poly:duv c0 c1 c2) x)", &env).as_field().unwrap();
        let horner_r = eval_str("(tadd Field Field c0 (tmul Field Field x (tadd Field Field c1 (tmul Field Field x c2))))", &env).as_field().unwrap();
        prop_assert_eq!(poly_r, horner_r);
    }

    #[test]
    fn poly_add_commutative(
        a0 in any::<u64>(), a1 in any::<u64>(),
        b0 in any::<u64>(), b1 in any::<u64>(),
        x_val in any::<u64>()
    ) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)),
            ("b0", fr_from_u64(b0)), ("b1", fr_from_u64(b1)),
            ("x", fr_from_u64(x_val)),
        ]);

        let r1 = eval_str("(teval DensePoly (tadd DensePoly DensePoly (poly:duv a0 a1) (poly:duv b0 b1)) x)", &env).as_field().unwrap();
        let r2 = eval_str("(teval DensePoly (tadd DensePoly DensePoly (poly:duv b0 b1) (poly:duv a0 a1)) x)", &env).as_field().unwrap();
        prop_assert_eq!(r1, r2);
    }

    #[test]
    fn poly_mul_commutative(
        a0 in any::<u64>(), a1 in any::<u64>(),
        b0 in any::<u64>(), b1 in any::<u64>(),
        x_val in any::<u64>()
    ) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)),
            ("b0", fr_from_u64(b0)), ("b1", fr_from_u64(b1)),
            ("x", fr_from_u64(x_val)),
        ]);

        let r1 = eval_str("(teval DensePoly (tmul DensePoly DensePoly (poly:duv a0 a1) (poly:duv b0 b1)) x)", &env).as_field().unwrap();
        let r2 = eval_str("(teval DensePoly (tmul DensePoly DensePoly (poly:duv b0 b1) (poly:duv a0 a1)) x)", &env).as_field().unwrap();
        prop_assert_eq!(r1, r2);
    }

    #[test]
    fn poly_eval_at_zero_is_constant_term(c0 in any::<u64>(), c1 in any::<u64>(), c2 in any::<u64>()) {
        let env = env_with_fields(&[
            ("c0", fr_from_u64(c0)), ("c1", fr_from_u64(c1)), ("c2", fr_from_u64(c2)),
        ]);

        let r = eval_str("(teval DensePoly (poly:duv c0 c1 c2) 0)", &env).as_field().unwrap();
        prop_assert_eq!(r, fr_from_u64(c0));
    }
}

// ── Array Property Tests (SMT theory-of-arrays axioms) ──

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn select_store_same_index(
        a_val in any::<u64>(), b_val in any::<u64>(), c_val in any::<u64>(),
        v_val in any::<u64>(), idx in 0u64..3u64
    ) {
        let env = env_with_fields(&[
            ("a", fr_from_u64(a_val)), ("b", fr_from_u64(b_val)),
            ("c", fr_from_u64(c_val)), ("v", fr_from_u64(v_val)),
        ]);
        let expr = format!("(tselect Field (tstore Field (mkarray a b c) {idx} v) {idx})");
        let r = eval_str(&expr, &env).as_field().unwrap();
        prop_assert_eq!(r, fr_from_u64(v_val));
    }

    #[test]
    fn store_store_same_index(
        a_val in any::<u64>(), b_val in any::<u64>(), c_val in any::<u64>(),
        v1_val in any::<u64>(), v2_val in any::<u64>(), idx in 0u64..3u64
    ) {
        let env = env_with_fields(&[
            ("a", fr_from_u64(a_val)), ("b", fr_from_u64(b_val)),
            ("c", fr_from_u64(c_val)), ("v1", fr_from_u64(v1_val)), ("v2", fr_from_u64(v2_val)),
        ]);
        for i in 0..3u64 {
            let lhs = format!("(tselect Field (tstore Field (tstore Field (mkarray a b c) {idx} v1) {idx} v2) {i})");
            let rhs = format!("(tselect Field (tstore Field (mkarray a b c) {idx} v2) {i})");
            let l = eval_str(&lhs, &env).as_field().unwrap();
            let r = eval_str(&rhs, &env).as_field().unwrap();
            prop_assert_eq!(l, r);
        }
    }

    #[test]
    fn alen_store_invariant(
        a_val in any::<u64>(), b_val in any::<u64>(), c_val in any::<u64>(),
        v_val in any::<u64>(), idx in 0u64..3u64
    ) {
        let env = env_with_fields(&[
            ("a", fr_from_u64(a_val)), ("b", fr_from_u64(b_val)),
            ("c", fr_from_u64(c_val)), ("v", fr_from_u64(v_val)),
        ]);
        let lhs_expr = format!("(alen (tstore Field (mkarray a b c) {idx} v))");
        let lhs = eval_str(&lhs_expr, &env);
        let rhs = eval_str("(alen (mkarray a b c))", &env);
        prop_assert_eq!(lhs, rhs);
    }
}

// ── Extended Polynomial Property Tests ──

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn poly_add_neg_is_zero(c0 in any::<u64>(), c1 in any::<u64>(), c2 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[
            ("c0", fr_from_u64(c0)), ("c1", fr_from_u64(c1)), ("c2", fr_from_u64(c2)),
            ("x", fr_from_u64(x)),
        ]);
        let r = eval_str("(teval DensePoly (tadd DensePoly DensePoly (poly:duv c0 c1 c2) (tneg DensePoly (poly:duv c0 c1 c2))) x)", &env).as_field().unwrap();
        prop_assert!(r.is_zero());
    }

    #[test]
    fn poly_sub_self_is_zero(c0 in any::<u64>(), c1 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[
            ("c0", fr_from_u64(c0)), ("c1", fr_from_u64(c1)), ("x", fr_from_u64(x)),
        ]);
        let r = eval_str("(teval DensePoly (tadd DensePoly DensePoly (poly:duv c0 c1) (tneg DensePoly (poly:duv c0 c1))) x)", &env).as_field().unwrap();
        prop_assert!(r.is_zero());
    }

    #[test]
    fn poly_scale_distributive(
        a0 in any::<u64>(), a1 in any::<u64>(),
        b0 in any::<u64>(), b1 in any::<u64>(),
        c_val in any::<u64>(), x_val in any::<u64>()
    ) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)),
            ("b0", fr_from_u64(b0)), ("b1", fr_from_u64(b1)),
            ("c", fr_from_u64(c_val)), ("x", fr_from_u64(x_val)),
        ]);
        // c * (p + q) == c*p + c*q
        let lhs = eval_str("(teval DensePoly (tscale DensePoly c (tadd DensePoly DensePoly (poly:duv a0 a1) (poly:duv b0 b1))) x)", &env).as_field().unwrap();
        let rhs = eval_str("(teval DensePoly (tadd DensePoly DensePoly (tscale DensePoly c (poly:duv a0 a1)) (tscale DensePoly c (poly:duv b0 b1))) x)", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[test]
    fn mle_hypercube_eval_matches_values(
        v0 in any::<u64>(), v1 in any::<u64>(), v2 in any::<u64>(), v3 in any::<u64>()
    ) {
        let env = env_with_fields(&[
            ("v0", fr_from_u64(v0)), ("v1", fr_from_u64(v1)),
            ("v2", fr_from_u64(v2)), ("v3", fr_from_u64(v3)),
        ]);
        let r00 = eval_str("(teval DenseMLE (poly:dmle 2 (mkarray v0 v1 v2 v3)) (mkarray 0 0))", &env).as_field().unwrap();
        prop_assert_eq!(r00, fr_from_u64(v0));

        let r10 = eval_str("(teval DenseMLE (poly:dmle 2 (mkarray v0 v1 v2 v3)) (mkarray 1 0))", &env).as_field().unwrap();
        prop_assert_eq!(r10, fr_from_u64(v1));

        let r01 = eval_str("(teval DenseMLE (poly:dmle 2 (mkarray v0 v1 v2 v3)) (mkarray 0 1))", &env).as_field().unwrap();
        prop_assert_eq!(r01, fr_from_u64(v2));

        let r11 = eval_str("(teval DenseMLE (poly:dmle 2 (mkarray v0 v1 v2 v3)) (mkarray 1 1))", &env).as_field().unwrap();
        prop_assert_eq!(r11, fr_from_u64(v3));
    }

    // ── Sparse UV matches Dense UV evaluation ──

    #[test]
    fn sparse_uv_matches_dense(a0 in any::<u64>(), a1 in any::<u64>(), x_val in any::<u64>()) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)), ("x", fr_from_u64(x_val)),
        ]);
        let dense = eval_str("(teval DensePoly (poly:duv a0 a1) x)", &env).as_field().unwrap();
        let sparse = eval_str("(teval SparsePoly (poly:suv 0 a0 1 a1) x)", &env).as_field().unwrap();
        prop_assert_eq!(dense, sparse);
    }
}
