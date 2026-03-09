// arkΣΠ Language & Runtime — Demo and Test Runner
//
// Exercises the full arkΣΠ language: parsing, evaluation, and correctness
// verification against arkworks. Outputs test results as JSON.

use ark_bls12_381::{Fr, G1Projective};
use ark_ec::CurveGroup;
use ark_ff::{UniformRand, Zero};
use ark_std::rand::SeedableRng;
use ark_sigma_pi::{eval, ArkLang, Env, EvalError, Value};
use egg::RecExpr;
use rand::rngs::StdRng;
use serde::Serialize;
use std::collections::HashMap;
use std::time::Instant;

#[derive(Debug, Serialize)]
struct TestResult {
    category: String,
    test_name: String,
    passed: bool,
    details: String,
    time_us: f64,
}

fn eval_str(s: &str, env: &Env) -> Result<Value, EvalError> {
    let expr: RecExpr<ArkLang> = s.parse().expect("parse failed");
    eval(&expr, env)
}

fn empty_env() -> Env {
    HashMap::new()
}

fn main() {
    let mut results: Vec<TestResult> = Vec::new();
    let mut rng = StdRng::seed_from_u64(42);

    println!("=== arkΣΠ Language & Runtime Demo ===\n");

    // ═══════════════════════════════════════════════
    // 1. FIELD ARITHMETIC (generic add/mul/neg)
    // ═══════════════════════════════════════════════
    println!("--- Field Arithmetic ---");

    let field_tests = vec![
        ("add basic", "(add Field Field 3 7)", 10i64),
        ("sub via neg", "(add Field Field 10 (neg Int 3))", 7),
        ("mul basic", "(mul Int Int 6 7)", 42),
        ("additive identity", "(add Field Field 42 0)", 42),
        ("multiplicative identity", "(mul Int Int 42 1)", 42),
        ("mul by zero", "(mul Int Int 42 0)", 0),
        ("double negation", "(neg Int (neg Int 5))", 5),
        ("sub self", "(add Field Field 99 (neg Int 99))", 0),
        ("nested add", "(add Field Field (add Field Field 1 2) (add Field Field 3 4))", 10),
        ("distributivity", "(mul Int Int 3 (add Int Int 4 5))", 27),
        ("power", "(pow Field (coerce Int Field 2) 10)", 1024),
    ];

    for (name, expr, expected) in &field_tests {
        let start = Instant::now();
        let result = eval_str(expr, &empty_env());
        let elapsed = start.elapsed().as_micros() as f64;

        let passed = match &result {
            Ok(v) => *v == Value::Int(*expected),
            Err(_) => false,
        };

        let details = if passed {
            format!("{} = {} ✓", expr, expected)
        } else {
            format!("{} expected {}, got {:?}", expr, expected, result)
        };

        println!("  {}: {}", name, if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_arithmetic".into(),
            test_name: name.to_string(),
            passed,
            details,
            time_us: elapsed,
        });
    }

    // Inverse
    {
        let start = Instant::now();
        let r = eval_str("(mul Field Field 3 (inv Field (coerce Int Field 3)))", &empty_env());
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = matches!(&r, Ok(v) if *v == Value::Int(1));
        println!("  inv*self=1: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_arithmetic".into(),
            test_name: "inverse_self_product".into(),
            passed,
            details: format!("3 * inv(3) = {:?}", r),
            time_us: elapsed,
        });
    }

    {
        let start = Instant::now();
        let r = eval_str("(mul Field Field 42 (inv Field (coerce Int Field 7)))", &empty_env());
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = matches!(&r, Ok(v) if *v == Value::Int(6));
        println!("  div: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_arithmetic".into(),
            test_name: "division".into(),
            passed,
            details: format!("42 / 7 = {:?}", r),
            time_us: elapsed,
        });
    }

    {
        let start = Instant::now();
        let r = eval_str("(inv Field (coerce Int Field 0))", &empty_env());
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = matches!(&r, Err(EvalError::DivisionByZero));
        println!("  div-by-zero: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_arithmetic".into(),
            test_name: "division_by_zero".into(),
            passed,
            details: format!("inv(0) = {:?}", r),
            time_us: elapsed,
        });
    }

    // Field arithmetic with random values
    println!("\n--- Field Arithmetic (Random Values) ---");
    {
        let a = Fr::rand(&mut rng);
        let b = Fr::rand(&mut rng);
        let mut env = empty_env();
        env.insert("a".into(), Value::Field(a));
        env.insert("b".into(), Value::Field(b));

        let start = Instant::now();
        let r1 = eval_str("(add Field Field a b)", &env).unwrap().as_field().unwrap();
        let r2 = eval_str("(add Field Field b a)", &env).unwrap().as_field().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = r1 == r2;
        println!("  add commutativity: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_properties".into(),
            test_name: "add_commutativity".into(),
            passed,
            details: "a+b == b+a with random a,b".into(),
            time_us: elapsed,
        });

        let start = Instant::now();
        let r1 = eval_str("(mul Field Field a b)", &env).unwrap().as_field().unwrap();
        let r2 = eval_str("(mul Field Field b a)", &env).unwrap().as_field().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = r1 == r2;
        println!("  mul commutativity: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_properties".into(),
            test_name: "mul_commutativity".into(),
            passed,
            details: "a*b == b*a with random a,b".into(),
            time_us: elapsed,
        });

        let c = Fr::rand(&mut rng);
        env.insert("c".into(), Value::Field(c));
        let start = Instant::now();
        let lhs = eval_str("(mul Field Field a (add Field Field b c))", &env).unwrap().as_field().unwrap();
        let rhs = eval_str("(add Field Field (mul Field Field a b) (mul Field Field a c))", &env).unwrap().as_field().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = lhs == rhs;
        println!("  distributivity: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_properties".into(),
            test_name: "distributivity".into(),
            passed,
            details: "a*(b+c) == a*b + a*c with random a,b,c".into(),
            time_us: elapsed,
        });

        let start = Instant::now();
        let lhs = eval_str("(add Field Field (add Field Field a b) c)", &env).unwrap().as_field().unwrap();
        let rhs = eval_str("(add Field Field a (add Field Field b c))", &env).unwrap().as_field().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = lhs == rhs;
        println!("  add associativity: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_properties".into(),
            test_name: "add_associativity".into(),
            passed,
            details: "(a+b)+c == a+(b+c) with random a,b,c".into(),
            time_us: elapsed,
        });

        let start = Instant::now();
        let lhs = eval_str("(mul Field Field (mul Field Field a b) c)", &env).unwrap().as_field().unwrap();
        let rhs = eval_str("(mul Field Field a (mul Field Field b c))", &env).unwrap().as_field().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = lhs == rhs;
        println!("  mul associativity: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_properties".into(),
            test_name: "mul_associativity".into(),
            passed,
            details: "(a*b)*c == a*(b*c) with random a,b,c".into(),
            time_us: elapsed,
        });

        let start = Instant::now();
        let r = eval_str("(add Field Field a (neg Field a))", &env).unwrap().as_field().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = r.is_zero();
        println!("  additive inverse: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_properties".into(),
            test_name: "additive_inverse".into(),
            passed,
            details: "a + (-a) == 0 with random a".into(),
            time_us: elapsed,
        });

        let start = Instant::now();
        let r = eval_str("(mul Field Field a (inv Field a))", &env).unwrap().as_field().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = r == Fr::from(1u64);
        println!("  mul inverse: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "field_properties".into(),
            test_name: "multiplicative_inverse".into(),
            passed,
            details: "a * inv(a) == 1 with random a".into(),
            time_us: elapsed,
        });
    }

    // ═══════════════════════════════════════════════
    // 2. CURVE OPERATIONS (generic add/neg/scale)
    // ═══════════════════════════════════════════════
    println!("\n--- Curve Operations ---");
    {
        let p = G1Projective::rand(&mut rng);
        let q = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("p".into(), Value::Curve(p));
        env.insert("q".into(), Value::Curve(q));

        let start = Instant::now();
        let r1 = eval_str("(add Curve Curve p q)", &env).unwrap().as_curve().unwrap();
        let r2 = eval_str("(add Curve Curve q p)", &env).unwrap().as_curve().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = r1.into_affine() == r2.into_affine();
        println!("  add commutativity: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "curve_operations".into(),
            test_name: "point_add_commutativity".into(),
            passed,
            details: "P+Q == Q+P".into(),
            time_us: elapsed,
        });

        let start = Instant::now();
        let r = eval_str("(add Curve Curve p (neg Curve p))", &env).unwrap().as_curve().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = r.is_zero();
        println!("  additive inverse: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "curve_operations".into(),
            test_name: "point_additive_inverse".into(),
            passed,
            details: "P + (-P) == O".into(),
            time_us: elapsed,
        });

        let start = Instant::now();
        let r1 = eval_str("(scale Curve 3 p)", &env).unwrap().as_curve().unwrap();
        let r2 = eval_str("(add Curve Curve p (add Curve Curve p p))", &env).unwrap().as_curve().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = r1.into_affine() == r2.into_affine();
        println!("  scalar mul consistency: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "curve_operations".into(),
            test_name: "scalar_mul_consistency".into(),
            passed,
            details: "3*P == P+P+P".into(),
            time_us: elapsed,
        });

        let s = Fr::rand(&mut rng);
        env.insert("s".into(), Value::Field(s));
        let start = Instant::now();
        let lhs = eval_str("(scale Curve s (add Curve Curve p q))", &env).unwrap().as_curve().unwrap();
        let rhs = eval_str("(add Curve Curve (scale Curve s p) (scale Curve s q))", &env).unwrap().as_curve().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = lhs.into_affine() == rhs.into_affine();
        println!("  scalar mul linearity: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "curve_operations".into(),
            test_name: "scalar_mul_linearity".into(),
            passed,
            details: "s*(P+Q) == s*P + s*Q".into(),
            time_us: elapsed,
        });

        let a = Fr::rand(&mut rng);
        let b = Fr::rand(&mut rng);
        env.insert("a".into(), Value::Field(a));
        env.insert("b".into(), Value::Field(b));
        let start = Instant::now();
        let lhs = eval_str("(scale Curve (add Field Field a b) p)", &env).unwrap().as_curve().unwrap();
        let rhs = eval_str("(add Curve Curve (scale Curve a p) (scale Curve b p))", &env).unwrap().as_curve().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = lhs.into_affine() == rhs.into_affine();
        println!("  scalar distributivity: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "curve_operations".into(),
            test_name: "scalar_distributivity".into(),
            passed,
            details: "(a+b)*P == a*P + b*P".into(),
            time_us: elapsed,
        });
    }

    // ═══════════════════════════════════════════════
    // 3. Σ/Π (replaces MSM)
    // ═══════════════════════════════════════════════
    println!("\n--- Indexed Sum (Σ) and Product (Π) ---");

    {
        let start = Instant::now();
        let v = eval_str("(Σ i 0 3 (get Int (array 10 20 30) i))", &empty_env()).unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = v == Value::Int(60);
        println!("  Σ sum: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "sigma_pi".into(),
            test_name: "sigma_sum".into(),
            passed,
            details: "Σ i=0..3 arr[i] = 60".into(),
            time_us: elapsed,
        });
    }

    {
        let start = Instant::now();
        let v = eval_str("(Π i 0 3 (get Int (array 2 3 5) i))", &empty_env()).unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let passed = v == Value::Int(30);
        println!("  Π product: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "sigma_pi".into(),
            test_name: "pi_product".into(),
            passed,
            details: "Π i=0..3 arr[i] = 30".into(),
            time_us: elapsed,
        });
    }

    // MSM via Σ
    {
        let p0 = G1Projective::rand(&mut rng);
        let p1 = G1Projective::rand(&mut rng);
        let a = Fr::rand(&mut rng);
        let b = Fr::rand(&mut rng);
        let mut env = empty_env();
        env.insert("a".into(), Value::Field(a));
        env.insert("b".into(), Value::Field(b));
        env.insert("P0".into(), Value::Curve(p0));
        env.insert("P1".into(), Value::Curve(p1));

        let start = Instant::now();
        let sigma_result = eval_str(
            "(Σ i 0 2 (scale Curve (get Field (array a b) i) (get Curve (array P0 P1) i)))",
            &env,
        ).unwrap().as_curve().unwrap();
        let elapsed = start.elapsed().as_micros() as f64;

        let expected = p0 * a + p1 * b;
        let passed = sigma_result.into_affine() == expected.into_affine();
        println!("  Σ MSM: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "sigma_pi".into(),
            test_name: "sigma_msm".into(),
            passed,
            details: "Σ s_i*P_i == MSM result".into(),
            time_us: elapsed,
        });
    }

    // ═══════════════════════════════════════════════
    // 4. POLYNOMIAL OPERATIONS
    // ═══════════════════════════════════════════════
    println!("\n--- Polynomial Operations ---");

    {
        let start = Instant::now();
        let v = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 1 2 3)) 5)", &empty_env())
            .unwrap()
            .as_field()
            .unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let expected = Fr::from(86u64);
        let passed = v == expected;
        println!("  poly eval: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "polynomial".into(),
            test_name: "poly_eval".into(),
            passed,
            details: "1+2x+3x^2 at x=5 = 86".into(),
            time_us: elapsed,
        });
    }

    {
        let start = Instant::now();
        let v = eval_str("(eval DensePoly (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 2)) (coerce (arrayof Field) DensePoly (array 3 4))) 10)", &empty_env())
            .unwrap()
            .as_field()
            .unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let expected = Fr::from(64u64);
        let passed = v == expected;
        println!("  poly add: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "polynomial".into(),
            test_name: "poly_add".into(),
            passed,
            details: "(1+2x)+(3+4x) at x=10 = 64".into(),
            time_us: elapsed,
        });
    }

    {
        let start = Instant::now();
        let v = eval_str("(eval DensePoly (mul DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 1)) (coerce (arrayof Field) DensePoly (array 1 1))) 3)", &empty_env())
            .unwrap()
            .as_field()
            .unwrap();
        let elapsed = start.elapsed().as_micros() as f64;
        let expected = Fr::from(16u64);
        let passed = v == expected;
        println!("  poly mul: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "polynomial".into(),
            test_name: "poly_mul".into(),
            passed,
            details: "(1+x)^2 at x=3 = 16".into(),
            time_us: elapsed,
        });
    }

    // Poly vs Horner (random)
    {
        let coeffs: Vec<Fr> = (0..5).map(|_| Fr::rand(&mut rng)).collect();
        let x = Fr::rand(&mut rng);
        let mut env = empty_env();
        env.insert("x".into(), Value::Field(x));
        for (i, c) in coeffs.iter().enumerate() {
            env.insert(format!("c{}", i).into(), Value::Field(*c));
        }

        let poly_result = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array c0 c1 c2 c3 c4)) x)", &env)
            .unwrap()
            .as_field()
            .unwrap();

        let horner_result = eval_str(
            "(add Field Field c0 (mul Field Field x (add Field Field c1 (mul Field Field x (add Field Field c2 (mul Field Field x (add Field Field c3 (mul Field Field x c4))))))))",
            &env,
        )
        .unwrap()
        .as_field()
        .unwrap();

        let passed = poly_result == horner_result;
        println!("  poly vs horner: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "polynomial".into(),
            test_name: "poly_vs_horner_random".into(),
            passed,
            details: "Polynomial eval matches Horner form with random coefficients".into(),
            time_us: 0.0,
        });
    }

    println!("\n--- Extended Polynomial Operations ---");

    {
        let v = eval_str("(eval DensePoly (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 2 3)) (neg DensePoly (coerce (arrayof Field) DensePoly (array 1 2)))) 2)", &empty_env()).unwrap();
        let passed = v == Value::Int(12);
        println!("  psub: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "polynomial".into(),
            test_name: "psub".into(),
            passed,
            details: "(1+2x+3x²)-(1+2x) at x=2 = 12".into(),
            time_us: 0.0,
        });
    }

    {
        let v = eval_str("(eval DensePoly (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 1)) (neg DensePoly (coerce (arrayof Field) DensePoly (array 1 1)))) 7)", &empty_env()).unwrap();
        let passed = v == Value::Int(0);
        println!("  pneg: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "polynomial".into(),
            test_name: "pneg".into(),
            passed,
            details: "p + (-p) at x=7 = 0".into(),
            time_us: 0.0,
        });
    }

    {
        let v = eval_str("(eval DensePoly (fst (div DensePoly (coerce (arrayof Field) DensePoly (array 1 3 2)) (coerce (arrayof Field) DensePoly (array 1 1)))) 5)", &empty_env()).unwrap();
        let passed = v == Value::Int(11);
        println!("  div quotient: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "polynomial".into(),
            test_name: "pdiv_quotient".into(),
            passed,
            details: "fst(div DensePoly (2x²+3x+1) (x+1)) at x=5 = 11".into(),
            time_us: 0.0,
        });
    }

    {
        let v = eval_str("(eval DensePoly (snd (div DensePoly (coerce (arrayof Field) DensePoly (array 1 0 1)) (coerce (arrayof Field) DensePoly (array 1 1)))) 999)", &empty_env()).unwrap();
        let passed = v == Value::Int(2);
        println!("  div remainder: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "polynomial".into(),
            test_name: "pdiv_remainder".into(),
            passed,
            details: "snd(div DensePoly (x²+1) (x+1)) = 2".into(),
            time_us: 0.0,
        });
    }

    {
        let v = eval_str("(deg DensePoly (coerce (arrayof Field) DensePoly (array 1 2 3)))", &empty_env()).unwrap();
        let passed = v == Value::Int(2);
        println!("  pdeg: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "polynomial".into(),
            test_name: "pdeg".into(),
            passed,
            details: "deg(1+2x+3x²) = 2".into(),
            time_us: 0.0,
        });
    }

    {
        let v = eval_str("(eval DensePoly (scale DensePoly 3 (coerce (arrayof Field) DensePoly (array 1 1))) 2)", &empty_env()).unwrap();
        let passed = v == Value::Int(9);
        println!("  pscale: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "polynomial".into(),
            test_name: "pscale".into(),
            passed,
            details: "3*(1+x) at x=2 = 9".into(),
            time_us: 0.0,
        });
    }

    // ═══════════════════════════════════════════════
    // 4b. MLE OPERATIONS
    // ═══════════════════════════════════════════════
    println!("\n--- Multilinear Extension (MLE) Operations ---");

    {
        let v = eval_str("(eval DenseMLE (coerce (arrayof Field) DenseMLE (array 1 2 3 4)) (array 1 0))", &empty_env()).unwrap();
        let passed = v == Value::Int(2);
        println!("  mle-eval: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "mle".into(),
            test_name: "mle_eval".into(),
            passed,
            details: "MLE(2vars) at (1,0) = 2".into(),
            time_us: 0.0,
        });
    }

    {
        let v = eval_str("(numvars DenseMLE (coerce (arrayof Field) DenseMLE (array 0 1 2 3 4 5 6 7)))", &empty_env()).unwrap();
        let passed = v == Value::Int(3);
        println!("  mle-nvars: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "mle".into(),
            test_name: "mle_nvars".into(),
            passed,
            details: "MLE(3vars) has 3 variables".into(),
            time_us: 0.0,
        });
    }

    {
        let v = eval_str(
            "(eval DenseMLE (fix (coerce (arrayof Field) DenseMLE (array 1 2 3 4)) (array 1)) (array 0))",
            &empty_env(),
        ).unwrap();
        let passed = v == Value::Int(2);
        println!("  mle-fix: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "mle".into(),
            test_name: "mle_fix".into(),
            passed,
            details: "fix x0=1 in MLE(2), eval at x1=0 = 2".into(),
            time_us: 0.0,
        });
    }

    {
        let v = eval_str(
            "(eval DenseMLE (add DenseMLE DenseMLE (coerce (arrayof Field) DenseMLE (array 1 0 0 0)) (coerce (arrayof Field) DenseMLE (array 0 0 0 1))) (array 1 1))",
            &empty_env(),
        ).unwrap();
        let passed = v == Value::Int(1);
        println!("  mle-add: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "mle".into(),
            test_name: "mle_add".into(),
            passed,
            details: "MLE add at (1,1) = 0+1 = 1".into(),
            time_us: 0.0,
        });
    }

    // ═══════════════════════════════════════════════
    // 4c. MULTIVARIATE POLYNOMIAL OPERATIONS
    // ═══════════════════════════════════════════════
    println!("\n--- Multivariate Polynomial Operations ---");

    {
        let v = eval_str(
            "(eval MVPoly (poly (ids x y) 5 (mul Field Field 2 x) (mul Field Field 3 y)) (array 2 7))",
            &empty_env(),
        ).unwrap();
        let passed = v == Value::Int(30);
        println!("  mveval: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "mvpoly".into(),
            test_name: "mveval".into(),
            passed,
            details: "2*x0+3*x1+5 at (2,7) = 30".into(),
            time_us: 0.0,
        });
    }

    {
        let v = eval_str(
            "(deg MVPoly (poly (ids x y) (mul Field Field (pow Field x 2) y)))",
            &empty_env(),
        ).unwrap();
        let passed = v == Value::Int(3);
        println!("  mvdeg: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult {
            category: "mvpoly".into(),
            test_name: "mvdeg".into(),
            passed,
            details: "deg(x0²·x1) = 3".into(),
            time_us: 0.0,
        });
    }

    // ═══════════════════════════════════════════════
    // 5. ARRAY OPERATIONS
    // ═══════════════════════════════════════════════
    println!("\n--- Array Operations ---");

    {
        let v = eval_str("(get Int (array 10 20 30) 1)", &empty_env()).unwrap();
        let passed = v == Value::Int(20);
        println!("  select: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "array".into(), test_name: "select".into(), passed, details: "arr[1] of [10,20,30] = 20".into(), time_us: 0.0 });
    }

    {
        let v = eval_str("(length (array 1 2 3 4 5))", &empty_env()).unwrap();
        let passed = v == Value::Int(5);
        println!("  alen: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "array".into(), test_name: "alen".into(), passed, details: "len([1,2,3,4,5]) = 5".into(), time_us: 0.0 });
    }

    {
        let r = eval_str("(get Int (array 1 2) 5)", &empty_env());
        let passed = matches!(r, Err(EvalError::IndexOutOfBounds { .. }));
        println!("  index out of bounds: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "array".into(), test_name: "index_out_of_bounds".into(), passed, details: "arr[5] of 2-element array raises error".into(), time_us: 0.0 });
    }

    {
        let v = eval_str("(get Int (set Int (array 1 2 3) 1 99) 1)", &empty_env()).unwrap();
        let passed = v == Value::Int(99);
        println!("  store: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "array".into(), test_name: "store".into(), passed, details: "store then select = 99".into(), time_us: 0.0 });
    }

    // ═══════════════════════════════════════════════
    // 6. LET BINDINGS AND CONTROL FLOW
    // ═══════════════════════════════════════════════
    println!("\n--- Let Bindings & Control Flow ---");

    {
        let v = eval_str("(let x 5 (mul Int Int x x))", &empty_env()).unwrap();
        let passed = v == Value::Int(25);
        println!("  let binding: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "control_flow".into(), test_name: "let_binding".into(), passed, details: "let x=5 in x*x = 25".into(), time_us: 0.0 });
    }

    {
        let v = eval_str("(let x 3 (let y 4 (add Field Field (mul Int Int x x) (mul Int Int y y))))", &empty_env()).unwrap();
        let passed = v == Value::Int(25);
        println!("  nested let: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "control_flow".into(), test_name: "nested_let".into(), passed, details: "let x=3 in let y=4 in x^2+y^2 = 25".into(), time_us: 0.0 });
    }

    {
        let v = eval_str("(if (eq Int 1 1) 42 0)", &empty_env()).unwrap();
        let passed = v == Value::Int(42);
        println!("  if-true: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "control_flow".into(), test_name: "if_true".into(), passed, details: "if 1==1 then 42 else 0 = 42".into(), time_us: 0.0 });
    }

    {
        let v = eval_str("(if (eq Int 1 2) 42 0)", &empty_env()).unwrap();
        let passed = v == Value::Int(0);
        println!("  if-false: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "control_flow".into(), test_name: "if_false".into(), passed, details: "if 1==2 then 42 else 0 = 0".into(), time_us: 0.0 });
    }

    // ═══════════════════════════════════════════════
    // 7. CONVERSION OPERATIONS
    // ═══════════════════════════════════════════════
    println!("\n--- Conversion Operations ---");

    {
        let v = eval_str("(eval DensePoly (coerce SparsePoly DensePoly (poly (ids x) 5 (mul Field Field 3 (pow Field x 2)))) 2)", &empty_env()).unwrap();
        let passed = v.as_field().unwrap() == Fr::from(17u64);
        println!("  densify sparse UV: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "conversions".into(), test_name: "densify_suv".into(), passed, details: "densify(5+3x²) at x=2 = 17".into(), time_us: 0.0 });
    }

    {
        let v = eval_str("(eval SparsePoly (coerce DensePoly SparsePoly (coerce (arrayof Field) DensePoly (array 5 0 3))) 2)", &empty_env()).unwrap();
        let passed = v.as_field().unwrap() == Fr::from(17u64);
        println!("  sparsify dense UV: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "conversions".into(), test_name: "sparsify_duv".into(), passed, details: "sparsify(5+3x²) at x=2 = 17".into(), time_us: 0.0 });
    }

    {
        let v = eval_str("(eval DensePoly (coerce DenseMLE DensePoly (coerce (arrayof Field) DenseMLE (array 3 7))) 2)", &empty_env()).unwrap();
        let passed = v.as_field().unwrap() == Fr::from(11u64);
        println!("  as-uv from MLE: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "conversions".into(), test_name: "as_uv_mle".into(), passed, details: "1-var MLE[3,7] → UV, eval at 2 = 11".into(), time_us: 0.0 });
    }

    // ═══════════════════════════════════════════════
    // 8. INTEGRATION: S-expr roundtrip + e-graph
    // ═══════════════════════════════════════════════
    println!("\n--- Complex Integration Tests ---");

    {
        let expr_str = "(add Field Field (mul Field Field 3 x) (neg Field y))";
        let expr: RecExpr<ArkLang> = expr_str.parse().unwrap();
        let displayed = expr.to_string();
        let reparsed: RecExpr<ArkLang> = displayed.parse().unwrap();
        let passed = expr == reparsed;
        println!("  s-expr roundtrip: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "integration".into(), test_name: "sexpr_roundtrip".into(), passed, details: "parse → display → parse preserves expression".into(), time_us: 0.0 });
    }

    {
        use egg::{EGraph, Runner, Rewrite, rewrite};

        let expr: RecExpr<ArkLang> = "(add Field Field (mul Field Field 3 x) (mul Field Field 4 x))".parse().unwrap();
        let mut egraph: EGraph<ArkLang, ()> = EGraph::default();
        let _root = egraph.add_expr(&expr);

        let rules: Vec<Rewrite<ArkLang, ()>> = vec![
            rewrite!("add-comm"; "(add ?T ?V ?a ?b)" => "(add ?V ?T ?b ?a)"),
            rewrite!("mul-comm"; "(mul ?T ?V ?a ?b)" => "(mul ?V ?T ?b ?a)"),
        ];

        let runner = Runner::default()
            .with_egraph(egraph)
            .run(&rules);

        let egraph = runner.egraph;
        let n_classes = egraph.number_of_classes();
        let passed = n_classes > 0;
        println!("  e-graph integration: {} ({} e-classes)", if passed { "PASS" } else { "FAIL" }, n_classes);
        results.push(TestResult { category: "integration".into(), test_name: "egraph_integration".into(), passed, details: format!("{} e-classes after rewriting", n_classes), time_us: 0.0 });
    }

    // ═══════════════════════════════════════════════
    // 9. SPARSE POLYNOMIAL DEMO
    // ═══════════════════════════════════════════════
    println!("\n--- Sparse Polynomial Operations ---");

    {
        let v = eval_str("(eval SparsePoly (poly (ids x) 5 (mul Field Field 3 (pow Field x 2))) 2)", &empty_env()).unwrap();
        let passed = v.as_field().unwrap() == Fr::from(17u64);
        println!("  sparse UV eval: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "sparse_poly".into(), test_name: "spoly_eval".into(), passed, details: "5+3x^2 at x=2 = 17".into(), time_us: 0.0 });
    }

    {
        let v = eval_str(
            "(eval SparseMLE (coerce DenseMLE SparseMLE (coerce (arrayof Field) DenseMLE (array 10 0 0 20))) (array 0 0))",
            &empty_env(),
        ).unwrap();
        let passed = v.as_field().unwrap() == Fr::from(10u64);
        println!("  sparse MLE eval: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "sparse_poly".into(), test_name: "smle_eval".into(), passed, details: "sparse MLE(2 vars) at (0,0) = 10".into(), time_us: 0.0 });
    }

    // ═══════════════════════════════════════════════
    // 10. FFT / IFFT / DOMAIN
    // ═══════════════════════════════════════════════
    println!("\n--- FFT / IFFT / Domain ---");

    {
        let v = eval_str("(domain 4)", &empty_env()).unwrap();
        let arr = v.as_array().unwrap();
        let passed = arr.len() == 4 && arr[0].as_field().unwrap() == Fr::from(1u64);
        println!("  domain elements: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "fft".into(), test_name: "domain_4".into(), passed, details: "domain(4) returns 4 roots of unity starting with 1".into(), time_us: 0.0 });
    }

    {
        // FFT of constant poly [5]: all evals should be 5
        let v = eval_str("(fft DensePoly 4 (coerce (arrayof Field) DensePoly (array 5)))", &empty_env()).unwrap();
        let arr = v.as_array().unwrap();
        let passed = arr.len() == 4 && arr.iter().all(|e| e.as_field().unwrap() == Fr::from(5u64));
        println!("  fft constant poly: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "fft".into(), test_name: "fft_constant".into(), passed, details: "fft(4, poly[5]) = [5,5,5,5]".into(), time_us: 0.0 });
    }

    {
        // IFFT roundtrip: eval(ifft(fft(p)), x) == eval(p, x)
        let env = empty_env();
        let orig = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 3 5 7)) 10)", &env).unwrap().as_field().unwrap();
        let rt = eval_str("(eval DensePoly (ifft Array 4 (fft DensePoly 4 (coerce (arrayof Field) DensePoly (array 3 5 7)))) 10)", &env).unwrap().as_field().unwrap();
        let passed = orig == rt;
        println!("  ifft roundtrip: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "fft".into(), test_name: "ifft_roundtrip".into(), passed, details: "ifft(fft(p)) preserves eval".into(), time_us: 0.0 });
    }

    {
        // FFT from array input
        let env = empty_env();
        let from_poly = eval_str("(fft DensePoly 4 (coerce (arrayof Field) DensePoly (array 1 2 3)))", &env).unwrap();
        let from_arr = eval_str("(fft Array 4 (array 1 2 3))", &env).unwrap();
        let passed = from_poly == from_arr;
        println!("  fft from array: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "fft".into(), test_name: "fft_from_array".into(), passed, details: "fft(poly) == fft(array) for same coefficients".into(), time_us: 0.0 });
    }

    // ═══════════════════════════════════════════════
    // 11. SYMBOLIC POLYNOMIAL CONSTRUCTOR
    // ═══════════════════════════════════════════════
    println!("\n--- Symbolic Polynomial Constructor ---");

    {
        // Univariate: 3x² + 5x + 7 at x=2 = 29
        let v = eval_str("(eval SparsePoly (poly (ids x) (mul Field Field 3 (pow Field x 2)) (mul Field Field 5 x) 7) 2)", &empty_env()).unwrap();
        let passed = v.as_field().unwrap() == Fr::from(29u64);
        println!("  poly UV basic: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "symbolic_poly".into(), test_name: "poly_uv_basic".into(), passed, details: "3x²+5x+7 at x=2 = 29".into(), time_us: 0.0 });
    }

    {
        // Cross-check: two equivalent symbolic poly forms evaluate identically
        let env = empty_env();
        let sym = eval_str("(eval SparsePoly (poly (ids x) (mul Field Field 3 (pow Field x 2)) (mul Field Field 5 x) 7) 10)", &env).unwrap().as_field().unwrap();
        let sym2 = eval_str("(eval SparsePoly (poly (ids x) 7 (mul Field Field 5 x) (mul Field Field 3 (pow Field x 2))) 10)", &env).unwrap().as_field().unwrap();
        let passed = sym == sym2;
        println!("  poly UV cross-check: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "symbolic_poly".into(), test_name: "poly_uv_cross_check".into(), passed, details: "3x²+5x+7 term-order invariant at x=10".into(), time_us: 0.0 });
    }

    {
        // Multivariate: x² + y³ + 4 at (3, 2) = 21
        let v = eval_str("(eval MVPoly (poly (ids x y) (pow Field x 2) (pow Field y 3) 4) (array 3 2))", &empty_env()).unwrap();
        let passed = v.as_field().unwrap() == Fr::from(21u64);
        println!("  poly MV: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "symbolic_poly".into(), test_name: "poly_mv_basic".into(), passed, details: "x²+y³+4 at (3,2) = 21".into(), time_us: 0.0 });
    }

    {
        // Cross term: 2xy at (3, 5) = 30
        let v = eval_str("(eval MVPoly (poly (ids x y) (mul Field Field 2 (mul Field Field x y))) (array 3 5))", &empty_env()).unwrap();
        let passed = v.as_field().unwrap() == Fr::from(30u64);
        println!("  poly MV cross term: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "symbolic_poly".into(), test_name: "poly_mv_cross".into(), passed, details: "2xy at (3,5) = 30".into(), time_us: 0.0 });
    }

    // ═══════════════════════════════════════════════
    // 12. TUPLES
    // ═══════════════════════════════════════════════
    println!("\n--- Tuples ---");

    {
        let v = eval_str("(fst (pair 3 7))", &empty_env()).unwrap();
        let passed = v.as_field().unwrap() == Fr::from(3u64);
        println!("  fst pair: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "tuple".into(), test_name: "fst_pair".into(), passed, details: "fst(pair(3,7)) = 3".into(), time_us: 0.0 });
    }

    {
        let v = eval_str("(snd (pair 3 7))", &empty_env()).unwrap();
        let passed = v.as_field().unwrap() == Fr::from(7u64);
        println!("  snd pair: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "tuple".into(), test_name: "snd_pair".into(), passed, details: "snd(pair(3,7)) = 7".into(), time_us: 0.0 });
    }

    {
        // pdiv division identity: a = q*b + r
        let env = empty_env();
        let a = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 1 0 1)) 5)", &env).unwrap().as_field().unwrap();
        let q = eval_str("(eval DensePoly (fst (div DensePoly (coerce (arrayof Field) DensePoly (array 1 0 1)) (coerce (arrayof Field) DensePoly (array 1 1)))) 5)", &env).unwrap().as_field().unwrap();
        let b = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 1 1)) 5)", &env).unwrap().as_field().unwrap();
        let r = eval_str("(eval DensePoly (snd (div DensePoly (coerce (arrayof Field) DensePoly (array 1 0 1)) (coerce (arrayof Field) DensePoly (array 1 1)))) 5)", &env).unwrap().as_field().unwrap();
        let passed = a == q * b + r;
        println!("  div identity a=qb+r: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "tuple".into(), test_name: "pdiv_identity".into(), passed, details: "a = q*b + r for (x²+1)/(x+1)".into(), time_us: 0.0 });
    }

    // ═══════════════════════════════════════════════
    // 13. ARRAY ADDITION
    // ═══════════════════════════════════════════════
    println!("\n--- Array Addition ---");

    {
        let v = eval_str("(add (arrayof Field) (arrayof Field) (array 1 2 3) (array 4 5 6))", &empty_env()).unwrap().as_array().unwrap();
        let passed = v.len() == 3 && v[0].as_field().unwrap() == Fr::from(5u64)
            && v[1].as_field().unwrap() == Fr::from(7u64) && v[2].as_field().unwrap() == Fr::from(9u64);
        println!("  array add basic: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "array".into(), test_name: "array_add_basic".into(), passed, details: "[1,2,3]+[4,5,6]=[5,7,9]".into(), time_us: 0.0 });
    }

    {
        let v = eval_str("(add (arrayof Field) (arrayof Field) (array 1 2) (array 10 20 30))", &empty_env()).unwrap().as_array().unwrap();
        let passed = v.len() == 3 && v[2].as_field().unwrap() == Fr::from(30u64);
        println!("  array add diff lengths: {}", if passed { "PASS" } else { "FAIL" });
        results.push(TestResult { category: "array".into(), test_name: "array_add_diff_len".into(), passed, details: "[1,2]+[10,20,30]=[11,22,30]".into(), time_us: 0.0 });
    }

    // ═══════════════════════════════════════════════
    // 14. LANGUAGE STATISTICS
    // ═══════════════════════════════════════════════
    println!("\n--- Language Statistics ---");

    let lang_stats = serde_json::json!({
        "node_types": {
            "typed_arithmetic": ["add", "neg", "mul", "inv", "scale", "pow", "coerce"],
            "type_tags": ["Field", "Curve", "Int", "Bool", "DensePoly", "SparsePoly", "DenseMLE", "SparseMLE", "MVPoly", "Array", "Pair", "arrayof"],
            "eval_queries": ["eval", "deg", "numvars"],
            "symbolic_constructors": ["ids", "poly", "mle"],
            "poly_specific": ["div", "fix"],
            "tuples": ["pair", "fst", "snd"],
            "indexed": ["bound", "Σ", "Π"],
            "fft": ["domain", "fft", "ifft"],
            "array_ops": ["array", "length", "get", "set"],
            "control": ["let", "if"],
            "comparison": ["eq"],
            "literals": ["Num", "Symbol"],
        },
        "total_node_types": 43,
        "field_type": "BLS12-381 Fr (scalar field)",
        "curve_type": "BLS12-381 G1",
        "syntax": "S-expressions (egg-native)",
        "evaluation": "type-validated recursive with environment",
        "egg_compatible": true,
    });

    println!("  Total node types: 43");
    println!("  Typed arithmetic: 7 (add, neg, mul, inv, scale, pow, coerce)");
    println!("  Type tags: 12 (Field, Curve, Int, Bool, DensePoly, SparsePoly, DenseMLE, SparseMLE, MVPoly, Array, Pair, arrayof)");
    println!("  Evaluation & queries: 3 (eval, deg, numvars)");
    println!("  Symbolic constructors: 3 (ids, poly, mle)");
    println!("  Poly-specific: 2 (div, fix)");
    println!("  Tuples: 3 (pair, fst, snd)");
    println!("  Indexed Σ/Π: 3 (bound, Σ, Π)");
    println!("  FFT/domain: 3 (domain, fft, ifft)");
    println!("  Array: 4 (array, length, get, set)");
    println!("  Control flow: 2 (let, if)");
    println!("  Comparison: 1 (eq)");
    println!("  Literals: 2 (Num, Symbol)");

    // ═══════════════════════════════════════════════
    // SUMMARY
    // ═══════════════════════════════════════════════
    let total = results.len();
    let passed = results.iter().filter(|r| r.passed).count();
    let failed = total - passed;

    println!("\n=== SUMMARY ===");
    println!("Total tests: {}", total);
    println!("Passed: {}", passed);
    println!("Failed: {}", failed);
    println!("Pass rate: {:.1}%", 100.0 * passed as f64 / total as f64);

    if failed > 0 {
        println!("\nFailed tests:");
        for r in results.iter().filter(|r| !r.passed) {
            println!("  - {}/{}: {}", r.category, r.test_name, r.details);
        }
    }

    let output = serde_json::json!({
        "tests": results,
        "summary": {
            "total": total,
            "passed": passed,
            "failed": failed,
            "pass_rate": format!("{:.1}%", 100.0 * passed as f64 / total as f64),
        },
        "language_stats": lang_stats,
    });
    std::fs::write("results.json", serde_json::to_string_pretty(&output).unwrap())
        .expect("Failed to write results.json");

    println!("\nResults written to results.json");

    if failed > 0 {
        std::process::exit(1);
    }
}
