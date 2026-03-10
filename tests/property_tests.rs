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

        let r1 = eval_str("(add Field Field a b)", &env).as_field().unwrap();
        let r2 = eval_str("(add Field Field b a)", &env).as_field().unwrap();
        prop_assert_eq!(r1, r2);
    }

    #[test]
    fn field_mul_commutative(a_val in any::<u64>(), b_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let b = fr_from_u64(b_val);
        let env = env_with_fields(&[("a", a), ("b", b)]);

        let r1 = eval_str("(mul Field Field a b)", &env).as_field().unwrap();
        let r2 = eval_str("(mul Field Field b a)", &env).as_field().unwrap();
        prop_assert_eq!(r1, r2);
    }

    #[test]
    fn field_add_associative(a_val in any::<u64>(), b_val in any::<u64>(), c_val in any::<u64>()) {
        let (a, b, c) = (fr_from_u64(a_val), fr_from_u64(b_val), fr_from_u64(c_val));
        let env = env_with_fields(&[("a", a), ("b", b), ("c", c)]);

        let lhs = eval_str("(add Field Field (add Field Field a b) c)", &env).as_field().unwrap();
        let rhs = eval_str("(add Field Field a (add Field Field b c))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[test]
    fn field_mul_associative(a_val in any::<u64>(), b_val in any::<u64>(), c_val in any::<u64>()) {
        let (a, b, c) = (fr_from_u64(a_val), fr_from_u64(b_val), fr_from_u64(c_val));
        let env = env_with_fields(&[("a", a), ("b", b), ("c", c)]);

        let lhs = eval_str("(mul Field Field (mul Field Field a b) c)", &env).as_field().unwrap();
        let rhs = eval_str("(mul Field Field a (mul Field Field b c))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[test]
    fn field_distributive(a_val in any::<u64>(), b_val in any::<u64>(), c_val in any::<u64>()) {
        let (a, b, c) = (fr_from_u64(a_val), fr_from_u64(b_val), fr_from_u64(c_val));
        let env = env_with_fields(&[("a", a), ("b", b), ("c", c)]);

        let lhs = eval_str("(mul Field Field a (add Field Field b c))", &env).as_field().unwrap();
        let rhs = eval_str("(add Field Field (mul Field Field a b) (mul Field Field a c))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[test]
    fn field_additive_identity(a_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(add Field Field a 0)", &env).as_field().unwrap();
        prop_assert_eq!(r, a);
    }

    #[test]
    fn field_multiplicative_identity(a_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(mul Field Field a 1)", &env).as_field().unwrap();
        prop_assert_eq!(r, a);
    }

    #[test]
    fn field_additive_inverse(a_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(add Field Field a (neg Field a))", &env).as_field().unwrap();
        prop_assert!(r.is_zero());
    }

    #[test]
    fn field_multiplicative_inverse(a_val in 1u64..u64::MAX) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(mul Field Field a (inv Field a))", &env).as_field().unwrap();
        prop_assert_eq!(r, Fr::from(1u64));
    }

    #[test]
    fn field_double_negation(a_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(neg Field (neg Field a))", &env).as_field().unwrap();
        prop_assert_eq!(r, a);
    }

    #[test]
    fn field_sub_is_add_neg(a_val in any::<u64>(), b_val in any::<u64>()) {
        let (a, b) = (fr_from_u64(a_val), fr_from_u64(b_val));
        let env = env_with_fields(&[("a", a), ("b", b)]);

        // a - b = a + (-b)
        let r = eval_str("(add Field Field a (neg Field b))", &env).as_field().unwrap();
        prop_assert_eq!(r, a - b);
    }

    #[test]
    fn field_mul_by_zero(a_val in any::<u64>()) {
        let a = fr_from_u64(a_val);
        let env = env_with_fields(&[("a", a)]);

        let r = eval_str("(mul Field Field a 0)", &env).as_field().unwrap();
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

        let r1 = eval_str("(add Curve Curve p q)", &env).as_curve().unwrap();
        let r2 = eval_str("(add Curve Curve q p)", &env).as_curve().unwrap();
        prop_assert_eq!(r1.into_affine(), r2.into_affine());
    }

    #[test]
    fn curve_additive_inverse(seed in any::<u64>()) {
        let mut rng = StdRng::seed_from_u64(seed);
        let p = G1Projective::rand(&mut rng);

        let mut env: Env = HashMap::new();
        env.insert("p".into(), Value::Curve(p));

        let r = eval_str("(add Curve Curve p (neg Curve p))", &env).as_curve().unwrap();
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
        let lhs = eval_str("(mul Field Curve s (add Curve Curve p q))", &env).as_curve().unwrap();
        let rhs = eval_str("(add Curve Curve (mul Field Curve s p) (mul Field Curve s q))", &env).as_curve().unwrap();
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
        let lhs = eval_str("(mul Field Curve (add Field Field a b) p)", &env).as_curve().unwrap();
        let rhs = eval_str("(add Curve Curve (mul Field Curve a p) (mul Field Curve b p))", &env).as_curve().unwrap();
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

        // Σ i=0..2 mul(Field, s_i, P_i) == a*P + b*Q
        let sigma_r = eval_str(
            "(Σ i 0 2 (mul Field Curve (get Field (array a b) i) (get Curve (array p q) i)))",
            &env,
        ).as_curve().unwrap();
        let manual_r = eval_str("(add Curve Curve (mul Field Curve a p) (mul Field Curve b q))", &env).as_curve().unwrap();
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

        let poly_r = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array c0 c1 c2)) x)", &env).as_field().unwrap();
        let horner_r = eval_str("(add Field Field c0 (mul Field Field x (add Field Field c1 (mul Field Field x c2))))", &env).as_field().unwrap();
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

        let r1 = eval_str("(eval DensePoly (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array a0 a1)) (coerce (arrayof Field) DensePoly (array b0 b1))) x)", &env).as_field().unwrap();
        let r2 = eval_str("(eval DensePoly (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array b0 b1)) (coerce (arrayof Field) DensePoly (array a0 a1))) x)", &env).as_field().unwrap();
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

        let r1 = eval_str("(eval DensePoly (mul DensePoly DensePoly (coerce (arrayof Field) DensePoly (array a0 a1)) (coerce (arrayof Field) DensePoly (array b0 b1))) x)", &env).as_field().unwrap();
        let r2 = eval_str("(eval DensePoly (mul DensePoly DensePoly (coerce (arrayof Field) DensePoly (array b0 b1)) (coerce (arrayof Field) DensePoly (array a0 a1))) x)", &env).as_field().unwrap();
        prop_assert_eq!(r1, r2);
    }

    #[test]
    fn poly_eval_at_zero_is_constant_term(c0 in any::<u64>(), c1 in any::<u64>(), c2 in any::<u64>()) {
        let env = env_with_fields(&[
            ("c0", fr_from_u64(c0)), ("c1", fr_from_u64(c1)), ("c2", fr_from_u64(c2)),
        ]);

        let r = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array c0 c1 c2)) 0)", &env).as_field().unwrap();
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
        let expr = format!("(get Field (set Field (array a b c) {idx} v) {idx})");
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
            let lhs = format!("(get Field (set Field (set Field (array a b c) {idx} v1) {idx} v2) {i})");
            let rhs = format!("(get Field (set Field (array a b c) {idx} v2) {i})");
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
        let lhs_expr = format!("(length (set Field (array a b c) {idx} v))");
        let lhs = eval_str(&lhs_expr, &env);
        let rhs = eval_str("(length (array a b c))", &env);
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
        let r = eval_str("(eval DensePoly (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array c0 c1 c2)) (neg DensePoly (coerce (arrayof Field) DensePoly (array c0 c1 c2)))) x)", &env).as_field().unwrap();
        prop_assert!(r.is_zero());
    }

    #[test]
    fn poly_sub_self_is_zero(c0 in any::<u64>(), c1 in any::<u64>(), x in any::<u64>()) {
        let env = env_with_fields(&[
            ("c0", fr_from_u64(c0)), ("c1", fr_from_u64(c1)), ("x", fr_from_u64(x)),
        ]);
        let r = eval_str("(eval DensePoly (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array c0 c1)) (neg DensePoly (coerce (arrayof Field) DensePoly (array c0 c1)))) x)", &env).as_field().unwrap();
        prop_assert!(r.is_zero());
    }

    #[test]
    fn poly_scalar_mul_distributive(
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
        let lhs = eval_str("(eval DensePoly (mul Field DensePoly c (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array a0 a1)) (coerce (arrayof Field) DensePoly (array b0 b1)))) x)", &env).as_field().unwrap();
        let rhs = eval_str("(eval DensePoly (add DensePoly DensePoly (mul Field DensePoly c (coerce (arrayof Field) DensePoly (array a0 a1))) (mul Field DensePoly c (coerce (arrayof Field) DensePoly (array b0 b1)))) x)", &env).as_field().unwrap();
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
        let r00 = eval_str("(eval DenseMLE (coerce (arrayof Field) DenseMLE (array v0 v1 v2 v3)) (array 0 0))", &env).as_field().unwrap();
        prop_assert_eq!(r00, fr_from_u64(v0));

        let r10 = eval_str("(eval DenseMLE (coerce (arrayof Field) DenseMLE (array v0 v1 v2 v3)) (array 1 0))", &env).as_field().unwrap();
        prop_assert_eq!(r10, fr_from_u64(v1));

        let r01 = eval_str("(eval DenseMLE (coerce (arrayof Field) DenseMLE (array v0 v1 v2 v3)) (array 0 1))", &env).as_field().unwrap();
        prop_assert_eq!(r01, fr_from_u64(v2));

        let r11 = eval_str("(eval DenseMLE (coerce (arrayof Field) DenseMLE (array v0 v1 v2 v3)) (array 1 1))", &env).as_field().unwrap();
        prop_assert_eq!(r11, fr_from_u64(v3));
    }

    // ── Sparse UV matches Dense UV evaluation ──

    #[test]
    fn sparse_uv_matches_dense(a0 in any::<u64>(), a1 in any::<u64>(), x_val in any::<u64>()) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)), ("x", fr_from_u64(x_val)),
        ]);
        let dense = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array a0 a1)) x)", &env).as_field().unwrap();
        let sparse = eval_str("(eval SparsePoly (poly (ids x) a0 (mul Field Field a1 x)) x)", &env).as_field().unwrap();
        prop_assert_eq!(dense, sparse);
    }

    // ═══════════════════════════════════════════════
    // Dot product (via Σ) properties
    // ═══════════════════════════════════════════════

    // Commutativity: Σ a_i*b_i = Σ b_i*a_i
    #[test]
    fn sigma_dot_commutativity(a0 in any::<u64>(), a1 in any::<u64>(), b0 in any::<u64>(), b1 in any::<u64>()) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)),
            ("b0", fr_from_u64(b0)), ("b1", fr_from_u64(b1)),
        ]);
        let lhs = eval_str("(Σ i 0 2 (mul Field Field (get Field (array a0 a1) i) (get Field (array b0 b1) i)))", &env).as_field().unwrap();
        let rhs = eval_str("(Σ i 0 2 (mul Field Field (get Field (array b0 b1) i) (get Field (array a0 a1) i)))", &env).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Linearity: Σ (c*a_i)*b_i = c * Σ a_i*b_i
    #[test]
    fn sigma_dot_linearity(c in any::<u64>(), a0 in any::<u64>(), a1 in any::<u64>(), b0 in any::<u64>(), b1 in any::<u64>()) {
        let env = env_with_fields(&[
            ("c", fr_from_u64(c)),
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)),
            ("b0", fr_from_u64(b0)), ("b1", fr_from_u64(b1)),
        ]);
        let lhs = eval_str(
            "(Σ i 0 2 (mul Field Field (mul Field Field c (get Field (array a0 a1) i)) (get Field (array b0 b1) i)))",
            &env
        ).as_field().unwrap();
        let rhs = eval_str(
            "(mul Field Field c (Σ i 0 2 (mul Field Field (get Field (array a0 a1) i) (get Field (array b0 b1) i))))",
            &env
        ).as_field().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Zero: Σ 0*a_i = 0
    #[test]
    fn sigma_dot_zero(a0 in any::<u64>(), a1 in any::<u64>()) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)),
        ]);
        let v = eval_str("(Σ i 0 2 (mul Field Field (get Field (array 0 0) i) (get Field (array a0 a1) i)))", &env).as_field().unwrap();
        prop_assert!(v.is_zero());
    }

    // Unit: Σ 1*a_i = Σ a_i
    #[test]
    fn sigma_dot_unit(a0 in any::<u64>(), a1 in any::<u64>(), a2 in any::<u64>()) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)), ("a2", fr_from_u64(a2)),
        ]);
        let dot_val = eval_str("(Σ i 0 3 (mul Field Field (get Field (array 1 1 1) i) (get Field (array a0 a1 a2) i)))", &env).as_field().unwrap();
        let sum_val = eval_str("(add Field Field a0 (add Field Field a1 a2))", &env).as_field().unwrap();
        prop_assert_eq!(dot_val, sum_val);
    }

    // ═══════════════════════════════════════════════
    // Hadamard (element-wise) product (via for) properties
    // ═══════════════════════════════════════════════

    // Commutativity: for(a_i*b_i) = for(b_i*a_i)
    #[test]
    fn for_hadamard_commutativity(a0 in any::<u64>(), a1 in any::<u64>(), b0 in any::<u64>(), b1 in any::<u64>()) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)),
            ("b0", fr_from_u64(b0)), ("b1", fr_from_u64(b1)),
        ]);
        let lhs = eval_str("(for i 0 2 (mul Field Field (get Field (array a0 a1) i) (get Field (array b0 b1) i)))", &env).as_array().unwrap();
        let rhs = eval_str("(for i 0 2 (mul Field Field (get Field (array b0 b1) i) (get Field (array a0 a1) i)))", &env).as_array().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Associativity: for(a_i * for(b_i*c_i)[i]) = for(for(a_i*b_i)[i] * c_i)
    #[test]
    fn for_hadamard_associativity(a0 in any::<u64>(), a1 in any::<u64>(), b0 in any::<u64>(), b1 in any::<u64>(), c0 in any::<u64>(), c1 in any::<u64>()) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)),
            ("b0", fr_from_u64(b0)), ("b1", fr_from_u64(b1)),
            ("c0", fr_from_u64(c0)), ("c1", fr_from_u64(c1)),
        ]);
        let lhs = eval_str(
            "(for i 0 2 (mul Field Field (get Field (array a0 a1) i) (get Field (for j 0 2 (mul Field Field (get Field (array b0 b1) j) (get Field (array c0 c1) j))) i)))",
            &env
        ).as_array().unwrap();
        let rhs = eval_str(
            "(for i 0 2 (mul Field Field (get Field (for j 0 2 (mul Field Field (get Field (array a0 a1) j) (get Field (array b0 b1) j))) i) (get Field (array c0 c1) i)))",
            &env
        ).as_array().unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // Unit: for(1*a_i) = [a0, a1, a2]
    #[test]
    fn for_hadamard_unit(a0 in any::<u64>(), a1 in any::<u64>(), a2 in any::<u64>()) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)), ("a2", fr_from_u64(a2)),
        ]);
        let result = eval_str("(for i 0 3 (mul Field Field (get Field (array 1 1 1) i) (get Field (array a0 a1 a2) i)))", &env).as_array().unwrap();
        let original = eval_str("(array a0 a1 a2)", &env).as_array().unwrap();
        prop_assert_eq!(result, original);
    }

    // Zero: for(0*a_i) = [0, 0]
    #[test]
    fn for_hadamard_zero(a0 in any::<u64>(), a1 in any::<u64>()) {
        let env = env_with_fields(&[
            ("a0", fr_from_u64(a0)), ("a1", fr_from_u64(a1)),
        ]);
        let result = eval_str("(for i 0 2 (mul Field Field (get Field (array 0 0) i) (get Field (array a0 a1) i)))", &env).as_array().unwrap();
        for v in result {
            prop_assert!(v.as_field().unwrap().is_zero());
        }
    }
}
