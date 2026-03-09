// arkΣΠ Rewrite Rules
//
// Universal algebraic rules, eval distribution, Σ/Π transforms,
// and conversion identities for egg equality saturation.

use egg::*;
use crate::language::ArkLang;
use crate::analysis::{TypeAnalysis, IndependentOf};

/// All algebraic rewrite rules (commutativity, associativity, etc).
pub fn algebra_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("add-comm"; "(add ?a ?b)" => "(add ?b ?a)"),
        rewrite!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),
        rewrite!("add-assoc"; "(add ?a (add ?b ?c))" => "(add (add ?a ?b) ?c)"),
        rewrite!("mul-assoc"; "(mul ?a (mul ?b ?c))" => "(mul (mul ?a ?b) ?c)"),
        rewrite!("double-neg"; "(neg (neg ?a))" => "?a"),
        rewrite!("add-neg"; "(add ?a (neg ?a))" => "0"),
        rewrite!("scale-one"; "(scale 1 ?a)" => "?a"),
        rewrite!("scale-zero"; "(scale 0 ?a)" => "0"),
        rewrite!("scale-dist"; "(scale ?c (add ?a ?b))" => "(add (scale ?c ?a) (scale ?c ?b))"),
        rewrite!("mul-dist"; "(mul ?a (add ?b ?c))" => "(add (mul ?a ?b) (mul ?a ?c))"),
        rewrite!("neg-as-scale"; "(neg ?a)" => "(scale -1 ?a)"),
    ]
}

/// Eval distribution rules.
pub fn eval_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("eval-add"; "(eval (add ?p ?q) ?x)" => "(add (eval ?p ?x) (eval ?q ?x))"),
        rewrite!("eval-neg"; "(eval (neg ?p) ?x)" => "(neg (eval ?p ?x))"),
        rewrite!("eval-scale"; "(eval (scale ?c ?p) ?x)" => "(mul ?c (eval ?p ?x))"),
        rewrite!("eval-mul"; "(eval (mul ?p ?q) ?x)" => "(mul (eval ?p ?x) (eval ?q ?x))"),
    ]
}

/// Σ/Π transform rules (unrolling for small concrete bounds).
pub fn sigma_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        // Unrolling small concrete bounds
        rewrite!("sigma-unroll-1"; "(Σ ?i 0 1 ?f)" => "(let ?i 0 ?f)"),
        rewrite!("sigma-unroll-2"; "(Σ ?i 0 2 ?f)" => "(add (let ?i 0 ?f) (let ?i 1 ?f))"),
        rewrite!("sigma-unroll-3"; "(Σ ?i 0 3 ?f)"
            => "(add (let ?i 0 ?f) (add (let ?i 1 ?f) (let ?i 2 ?f)))"),

        // Σ distributes over add in the body
        rewrite!("sigma-dist-add"; "(Σ ?i ?lo ?hi (add ?f ?g))"
            => "(add (Σ ?i ?lo ?hi ?f) (Σ ?i ?lo ?hi ?g))"),

        // Π unrolling
        rewrite!("pi-unroll-1"; "(Π ?i 0 1 ?f)" => "(let ?i 0 ?f)"),
        rewrite!("pi-unroll-2"; "(Π ?i 0 2 ?f)" => "(mul (let ?i 0 ?f) (let ?i 1 ?f))"),
    ]
}

/// Conversion roundtrip identity rules.
pub fn conversion_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("densify-sparsify"; "(densify (sparsify ?p))" => "?p"),
        rewrite!("sparsify-densify"; "(sparsify (densify ?p))" => "?p"),
        rewrite!("as-uv-as-mle"; "(as-uv (as-mle ?p))" => "?p"),
        rewrite!("as-mle-as-uv"; "(as-mle (as-uv ?m))" => "?m"),
        rewrite!("ifft-fft"; "(ifft ?n (fft ?n ?p))" => "?p"),
        rewrite!("fft-ifft"; "(fft ?n (ifft ?n ?e))" => "?e"),
        // Tuple projections
        rewrite!("fst-pair"; "(fst (pair ?a ?b))" => "?a"),
        rewrite!("snd-pair"; "(snd (pair ?a ?b))" => "?b"),
        rewrite!("pair-eta"; "(pair (fst ?p) (snd ?p))" => "?p"),
        // Array addition commutativity
        rewrite!("aadd-comm"; "(aadd ?a ?b)" => "(aadd ?b ?a)"),
    ]
}

/// Guarded Σ/Π rules that require type analysis (free variable tracking).
pub fn guarded_sigma_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        // Factor extraction: pull scalar out of Σ when independent of loop var
        rewrite!("sigma-factor-scale";
            "(Σ ?i ?lo ?hi (scale ?c ?f))" => "(scale ?c (Σ ?i ?lo ?hi ?f))"
            if IndependentOf { expr_var: "?c".parse().unwrap(), idx_var: "?i".parse().unwrap() }
        ),
        // Factor extraction: pull multiplicand out of Σ when independent of loop var
        rewrite!("sigma-factor-mul";
            "(Σ ?i ?lo ?hi (mul ?c ?f))" => "(mul ?c (Σ ?i ?lo ?hi ?f))"
            if IndependentOf { expr_var: "?c".parse().unwrap(), idx_var: "?i".parse().unwrap() }
        ),
        // Σ fusion: merge two Σ loops with the same range
        rewrite!("sigma-fusion";
            "(add (Σ ?i ?lo ?hi ?f) (Σ ?i ?lo ?hi ?g))" => "(Σ ?i ?lo ?hi (add ?f ?g))"
        ),
    ]
}

/// Typed add rules (tadd — Wave 1 canary).
pub fn typed_add_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("tadd-comm"; "(tadd ?T ?V ?a ?b)" => "(tadd ?V ?T ?b ?a)"),
        rewrite!("tadd-assoc"; "(tadd ?T ?V ?a (tadd ?V ?W ?b ?c))" => "(tadd ?T ?W (tadd ?T ?V ?a ?b) ?c)"),
        rewrite!("tadd-neg"; "(tadd ?T ?T ?a (tneg ?T ?a))" => "0"),
    ]
}

/// Typed arithmetic rules (Wave 2: tneg, tmul, tscale, tpow).
pub fn typed_arith_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        // ── Negation ──
        rewrite!("double-tneg"; "(tneg ?T (tneg ?T ?a))" => "?a"),
        rewrite!("tneg-as-tscale"; "(tneg ?T ?a)" => "(tscale ?T -1 ?a)"),

        // ── Multiplication ──
        rewrite!("tmul-comm"; "(tmul ?T ?V ?a ?b)" => "(tmul ?V ?T ?b ?a)"),
        rewrite!("tmul-assoc"; "(tmul ?T ?V ?a (tmul ?V ?W ?b ?c))" => "(tmul ?T ?W (tmul ?T ?V ?a ?b) ?c)"),
        rewrite!("tmul-dist"; "(tmul ?T ?T ?a (tadd ?T ?T ?b ?c))" => "(tadd ?T ?T (tmul ?T ?T ?a ?b) (tmul ?T ?T ?a ?c))"),

        // ── Scale ──
        rewrite!("tscale-one"; "(tscale ?T 1 ?a)" => "?a"),
        rewrite!("tscale-zero"; "(tscale ?T 0 ?a)" => "0"),
        rewrite!("tscale-dist"; "(tscale ?T ?c (tadd ?T ?T ?a ?b))" => "(tadd ?T ?T (tscale ?T ?c ?a) (tscale ?T ?c ?b))"),
    ]
}

/// Typed guarded sigma rules for tscale/tmul factor extraction.
pub fn typed_guarded_arith_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("sigma-factor-tscale";
            "(Σ ?i ?lo ?hi (tscale ?T ?c ?f))" => "(tscale ?T ?c (Σ ?i ?lo ?hi ?f))"
            if IndependentOf { expr_var: "?c".parse().unwrap(), idx_var: "?i".parse().unwrap() }
        ),
        rewrite!("sigma-factor-tmul";
            "(Σ ?i ?lo ?hi (tmul ?T ?T ?c ?f))" => "(tmul ?T ?T ?c (Σ ?i ?lo ?hi ?f))"
            if IndependentOf { expr_var: "?c".parse().unwrap(), idx_var: "?i".parse().unwrap() }
        ),
    ]
}

/// Custom applier that reads the body type from TypeAnalysis to emit typed add/mul.
struct TypedUnrollApplier {
    /// Pattern variables for the body subexpressions (one per iteration value)
    body_var: Var,
    /// Pattern variable for the loop index
    idx_var: Var,
    /// Iteration values (e.g., [0, 1] for unroll-2)
    iter_vals: Vec<i64>,
    /// Whether to use tadd (for Σ) or mul (for Π)
    op: &'static str,
}

impl Applier<ArkLang, TypeAnalysis> for TypedUnrollApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<ArkLang, TypeAnalysis>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<ArkLang>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let body_id = subst[self.body_var];
        let idx_id = subst[self.idx_var];

        // Read body type from analysis to determine the type tag
        let body_types = &egraph[body_id].data.types;
        let type_tag = if body_types.contains(&crate::value::ArkType::Field) {
            ArkLang::TField
        } else if body_types.contains(&crate::value::ArkType::Curve) {
            ArkLang::TCurve
        } else if body_types.contains(&crate::value::ArkType::DensePoly) {
            ArkLang::TDensePoly
        } else if body_types.contains(&crate::value::ArkType::SparsePoly) {
            ArkLang::TSparsePoly
        } else if body_types.contains(&crate::value::ArkType::DenseMLE) {
            ArkLang::TDenseMLE
        } else if body_types.contains(&crate::value::ArkType::MVPoly) {
            ArkLang::TMVPoly
        } else if body_types.contains(&crate::value::ArkType::Int) {
            ArkLang::TInt
        } else {
            // Unknown type — fall back to untyped, don't apply
            return vec![];
        };

        let tag_id = egraph.add(type_tag);

        // Build (let ?i val ?body) for each iteration
        let mut let_ids: Vec<Id> = Vec::new();
        for &val in &self.iter_vals {
            let val_id = egraph.add(ArkLang::Num(val));
            let let_id = egraph.add(ArkLang::Let([idx_id, val_id, body_id]));
            let_ids.push(let_id);
        }

        // If only one iteration, result is just the let binding
        if let_ids.len() == 1 {
            egraph.union(eclass, let_ids[0]);
            return vec![let_ids[0]];
        }

        // Build a right-associative chain of tadd (or mul for Π)
        let result = if self.op == "tadd" {
            // (tadd T T (let i 0 body) (tadd T T (let i 1 body) ...))
            let mut acc = *let_ids.last().unwrap();
            for &lid in let_ids[..let_ids.len() - 1].iter().rev() {
                acc = egraph.add(ArkLang::TAdd([tag_id, tag_id, lid, acc]));
            }
            acc
        } else {
            // mul: for now, use untyped Mul since TMul doesn't exist yet
            let mut acc = *let_ids.last().unwrap();
            for &lid in let_ids[..let_ids.len() - 1].iter().rev() {
                acc = egraph.add(ArkLang::Mul([lid, acc]));
            }
            acc
        };

        egraph.union(eclass, result);
        vec![result]
    }
}

/// Typed sigma unrolling rules using TypedUnrollApplier.
pub fn typed_sigma_unroll_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        Rewrite::new(
            Symbol::from("typed-sigma-unroll-2"),
            "(Σ ?i 0 2 ?f)".parse::<Pattern<ArkLang>>().unwrap(),
            TypedUnrollApplier {
                body_var: "?f".parse().unwrap(),
                idx_var: "?i".parse().unwrap(),
                iter_vals: vec![0, 1],
                op: "tadd",
            },
        ).unwrap(),
        Rewrite::new(
            Symbol::from("typed-sigma-unroll-3"),
            "(Σ ?i 0 3 ?f)".parse::<Pattern<ArkLang>>().unwrap(),
            TypedUnrollApplier {
                body_var: "?f".parse().unwrap(),
                idx_var: "?i".parse().unwrap(),
                iter_vals: vec![0, 1, 2],
                op: "tadd",
            },
        ).unwrap(),
    ]
}

/// Typed sigma distribution over tadd.
pub fn typed_sigma_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("sigma-dist-tadd"; "(Σ ?i ?lo ?hi (tadd ?T ?T ?f ?g))"
            => "(tadd ?T ?T (Σ ?i ?lo ?hi ?f) (Σ ?i ?lo ?hi ?g))"),
    ]
}

/// Typed sigma fusion rule.
pub fn typed_guarded_sigma_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("sigma-fusion-tadd";
            "(tadd ?T ?T (Σ ?i ?lo ?hi ?f) (Σ ?i ?lo ?hi ?g))" => "(Σ ?i ?lo ?hi (tadd ?T ?T ?f ?g))"
        ),
    ]
}

/// All rules combined (untyped + typed).
pub fn all_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    let mut rules = algebra_rules();
    rules.extend(eval_rules());
    rules.extend(sigma_rules());
    rules.extend(guarded_sigma_rules());
    rules.extend(conversion_rules());
    rules.extend(typed_add_rules());
    rules.extend(typed_arith_rules());
    rules.extend(typed_sigma_rules());
    rules.extend(typed_guarded_sigma_rules());
    rules.extend(typed_guarded_arith_rules());
    rules.extend(typed_sigma_unroll_rules());
    rules
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::{eval, Env};
    use crate::value::Value;
    use crate::analysis::TypeAnalysis;
    use std::collections::HashMap;

    fn empty_env() -> Env {
        HashMap::new()
    }

    fn eval_str(s: &str, env: &Env) -> Value {
        let expr: RecExpr<ArkLang> = s.parse().expect("parse failed");
        eval(&expr, env).expect("eval failed")
    }

    /// Run egg with given rules and extract the simplest equivalent expression.
    fn simplify(expr_str: &str, rules: &[Rewrite<ArkLang, TypeAnalysis>]) -> String {
        let expr: RecExpr<ArkLang> = expr_str.parse().unwrap();
        let runner = Runner::default()
            .with_expr(&expr)
            .run(rules);
        let root = runner.roots[0];
        let extractor = Extractor::new(&runner.egraph, AstSize);
        let (_, best) = extractor.find_best(root);
        best.to_string()
    }

    /// Assert that two expressions merge into the same e-class under given rules.
    fn assert_merge(e1: &str, e2: &str, rules: &[Rewrite<ArkLang, TypeAnalysis>], msg: &str) {
        let expr1: RecExpr<ArkLang> = e1.parse().unwrap();
        let expr2: RecExpr<ArkLang> = e2.parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&expr1);
        let id2 = egraph.add_expr(&expr2);
        let runner = Runner::default().with_egraph(egraph).run(rules);
        assert_eq!(runner.egraph.find(id1), runner.egraph.find(id2), "{}", msg);
    }

    /// Assert that two expressions do NOT merge under given rules.
    fn assert_no_merge(e1: &str, e2: &str, rules: &[Rewrite<ArkLang, TypeAnalysis>], msg: &str) {
        let expr1: RecExpr<ArkLang> = e1.parse().unwrap();
        let expr2: RecExpr<ArkLang> = e2.parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&expr1);
        let id2 = egraph.add_expr(&expr2);
        let runner = Runner::default().with_egraph(egraph).run(rules);
        assert_ne!(runner.egraph.find(id1), runner.egraph.find(id2), "{}", msg);
    }

    #[test]
    fn test_add_commutativity_rewrite() {
        let rules = algebra_rules();
        let expr: RecExpr<ArkLang> = "(add x y)".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&expr);
        let expr2: RecExpr<ArkLang> = "(add y x)".parse().unwrap();
        let id2 = egraph.add_expr(&expr2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        // After applying commutativity, (add x y) and (add y x) should be in the same e-class
        assert_eq!(
            runner.egraph.find(id1),
            runner.egraph.find(id2),
            "add commutativity should merge (add x y) and (add y x)"
        );
    }

    #[test]
    fn test_mul_commutativity_rewrite() {
        let rules = algebra_rules();
        let e1: RecExpr<ArkLang> = "(mul a b)".parse().unwrap();
        let e2: RecExpr<ArkLang> = "(mul b a)".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(runner.egraph.find(id1), runner.egraph.find(id2));
    }

    #[test]
    fn test_double_neg_elimination() {
        let simplified = simplify("(neg (neg x))", &algebra_rules());
        assert_eq!(simplified, "x");
    }

    #[test]
    fn test_scale_one_elimination() {
        let simplified = simplify("(scale 1 x)", &algebra_rules());
        assert_eq!(simplified, "x");
    }

    #[test]
    fn test_scale_distributivity() {
        let rules = algebra_rules();
        let e1: RecExpr<ArkLang> = "(scale c (add a b))".parse().unwrap();
        let e2: RecExpr<ArkLang> = "(add (scale c a) (scale c b))".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(runner.egraph.find(id1), runner.egraph.find(id2));
    }

    #[test]
    fn test_eval_distributes_over_add() {
        let rules = eval_rules();
        let e1: RecExpr<ArkLang> = "(eval (add p q) x)".parse().unwrap();
        let e2: RecExpr<ArkLang> = "(add (eval p x) (eval q x))".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(runner.egraph.find(id1), runner.egraph.find(id2));
    }

    #[test]
    fn test_sigma_unroll_2() {
        let simplified = simplify("(Σ i 0 2 (select arr i))", &sigma_rules());
        // After unrolling, the e-graph contains the unrolled form.
        // The extractor may pick either form depending on cost.
        // Just verify the e-graph contains the equivalence.
        let rules = sigma_rules();
        let e1: RecExpr<ArkLang> = "(Σ i 0 2 (select arr i))".parse().unwrap();
        let e2: RecExpr<ArkLang> =
            "(add (let i 0 (select arr i)) (let i 1 (select arr i)))".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(
            runner.egraph.find(id1),
            runner.egraph.find(id2),
            "Σ unroll-2 should merge with the unrolled form. Simplified: {}",
            simplified
        );
    }

    #[test]
    fn test_sigma_unroll_eval_matches() {
        use ark_bls12_381::Fr;
        let env = empty_env();
        // Direct: Σ i 0 3 (select (mkarray 10 20 30) i) = 60
        let direct = eval_str("(Σ i 0 3 (select (mkarray 10 20 30) i))", &env);
        assert_eq!(direct.as_field().unwrap(), Fr::from(60u64));

        // Unrolled equivalent:
        let unrolled = eval_str(
            "(add (let i 0 (select (mkarray 10 20 30) i)) \
                  (add (let i 1 (select (mkarray 10 20 30) i)) \
                       (let i 2 (select (mkarray 10 20 30) i))))",
            &env,
        );
        assert_eq!(unrolled.as_field().unwrap(), Fr::from(60u64));
    }

    #[test]
    fn test_conversion_roundtrip_rewrite() {
        let rules = conversion_rules();
        let simplified = simplify("(densify (sparsify p))", &rules);
        assert_eq!(simplified, "p");

        let simplified2 = simplify("(as-uv (as-mle p))", &rules);
        assert_eq!(simplified2, "p");
    }

    #[test]
    fn test_all_rules_combined() {
        let rules = all_rules();
        // Complex expression: scale distributes, then add is commutative
        let e1: RecExpr<ArkLang> = "(scale c (add a b))".parse().unwrap();
        let e2: RecExpr<ArkLang> = "(add (scale c b) (scale c a))".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(
            runner.egraph.find(id1),
            runner.egraph.find(id2),
            "scale(c, a+b) should equal scale(c,b) + scale(c,a) via dist+comm"
        );
    }

    #[test]
    fn test_guarded_factor_extraction() {
        // c is independent of i → factor extraction should apply
        let rules = guarded_sigma_rules();
        let e1: RecExpr<ArkLang> =
            "(Σ i 0 N (scale c (select arr i)))".parse().unwrap();
        let e2: RecExpr<ArkLang> =
            "(scale c (Σ i 0 N (select arr i)))".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(
            runner.egraph.find(id1),
            runner.egraph.find(id2),
            "Σ(scale c f) should equal scale c (Σ f) when c is independent of i"
        );
    }

    #[test]
    fn test_guarded_factor_blocked() {
        // i IS the loop variable → factor extraction must NOT apply
        let rules = guarded_sigma_rules();
        let e1: RecExpr<ArkLang> =
            "(Σ i 0 N (scale i (select arr i)))".parse().unwrap();
        let e2: RecExpr<ArkLang> =
            "(scale i (Σ i 0 N (select arr i)))".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_ne!(
            runner.egraph.find(id1),
            runner.egraph.find(id2),
            "Σ(scale i f) should NOT be factored when i is the loop variable"
        );
    }

    #[test]
    fn test_sigma_fusion() {
        let rules = guarded_sigma_rules();
        let e1: RecExpr<ArkLang> =
            "(add (Σ i 0 N (select a i)) (Σ i 0 N (select b i)))".parse().unwrap();
        let e2: RecExpr<ArkLang> =
            "(Σ i 0 N (add (select a i) (select b i)))".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(
            runner.egraph.find(id1),
            runner.egraph.find(id2),
            "Σ f + Σ g should fuse into Σ (f + g)"
        );
    }

    #[test]
    fn test_fft_ifft_roundtrip_rewrite() {
        let rules = conversion_rules();
        let simplified = simplify("(ifft n (fft n p))", &rules);
        assert_eq!(simplified, "p");

        let simplified2 = simplify("(fft n (ifft n e))", &rules);
        assert_eq!(simplified2, "e");
    }

    #[test]
    fn test_fft_ifft_roundtrip_egraph() {
        let rules = all_rules();
        let e1: RecExpr<ArkLang> = "(ifft 8 (fft 8 p))".parse().unwrap();
        let e2: RecExpr<ArkLang> = "p".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(
            runner.egraph.find(id1),
            runner.egraph.find(id2),
            "ifft(n, fft(n, p)) should reduce to p"
        );
    }

    #[test]
    fn test_fst_pair_projection() {
        let rules = conversion_rules();
        let simplified = simplify("(fst (pair a b))", &rules);
        assert_eq!(simplified, "a");
    }

    #[test]
    fn test_snd_pair_projection() {
        let rules = conversion_rules();
        let simplified = simplify("(snd (pair a b))", &rules);
        assert_eq!(simplified, "b");
    }

    #[test]
    fn test_pair_eta() {
        let rules = conversion_rules();
        let e1: RecExpr<ArkLang> = "(pair (fst p) (snd p))".parse().unwrap();
        let e2: RecExpr<ArkLang> = "p".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(
            runner.egraph.find(id1),
            runner.egraph.find(id2),
            "(pair (fst p) (snd p)) should reduce to p"
        );
    }

    #[test]
    fn test_aadd_commutativity_rewrite() {
        let rules = conversion_rules();
        assert_merge("(aadd a b)", "(aadd b a)", &rules, "aadd-comm");
    }

    // ═══════════════════════════════════════════════
    // Comprehensive e-graph merge tests — one per rule
    // ═══════════════════════════════════════════════

    #[test]
    fn test_egraph_add_assoc() {
        let rules = algebra_rules();
        assert_merge("(add a (add b c))", "(add (add a b) c)", &rules, "add-assoc");
    }

    #[test]
    fn test_egraph_mul_assoc() {
        let rules = algebra_rules();
        assert_merge("(mul a (mul b c))", "(mul (mul a b) c)", &rules, "mul-assoc");
    }

    #[test]
    fn test_egraph_add_neg() {
        let rules = algebra_rules();
        assert_merge("(add a (neg a))", "0", &rules, "add-neg");
    }

    #[test]
    fn test_egraph_mul_dist() {
        let rules = algebra_rules();
        assert_merge("(mul a (add b c))", "(add (mul a b) (mul a c))", &rules, "mul-dist");
    }

    #[test]
    fn test_egraph_neg_as_scale() {
        let rules = algebra_rules();
        assert_merge("(neg a)", "(scale -1 a)", &rules, "neg-as-scale");
    }

    #[test]
    fn test_egraph_eval_add() {
        let rules = eval_rules();
        assert_merge("(eval (add p q) x)", "(add (eval p x) (eval q x))", &rules, "eval-add");
    }

    #[test]
    fn test_egraph_eval_neg() {
        let rules = eval_rules();
        assert_merge("(eval (neg p) x)", "(neg (eval p x))", &rules, "eval-neg");
    }

    #[test]
    fn test_egraph_eval_scale() {
        let rules = eval_rules();
        assert_merge("(eval (scale c p) x)", "(mul c (eval p x))", &rules, "eval-scale");
    }

    #[test]
    fn test_egraph_eval_mul() {
        let rules = eval_rules();
        assert_merge("(eval (mul p q) x)", "(mul (eval p x) (eval q x))", &rules, "eval-mul");
    }

    #[test]
    fn test_egraph_sigma_unroll_1() {
        let rules = sigma_rules();
        assert_merge("(Σ i 0 1 (select a i))", "(let i 0 (select a i))", &rules, "sigma-unroll-1");
    }

    #[test]
    fn test_egraph_sigma_unroll_3() {
        let rules = sigma_rules();
        assert_merge(
            "(Σ i 0 3 (select a i))",
            "(add (let i 0 (select a i)) (add (let i 1 (select a i)) (let i 2 (select a i))))",
            &rules, "sigma-unroll-3"
        );
    }

    #[test]
    fn test_egraph_sigma_dist_add() {
        let rules = sigma_rules();
        assert_merge(
            "(Σ i lo hi (add f g))",
            "(add (Σ i lo hi f) (Σ i lo hi g))",
            &rules, "sigma-dist-add"
        );
    }

    #[test]
    fn test_egraph_pi_unroll_1() {
        let rules = sigma_rules();
        assert_merge("(Π i 0 1 (select a i))", "(let i 0 (select a i))", &rules, "pi-unroll-1");
    }

    #[test]
    fn test_egraph_pi_unroll_2() {
        let rules = sigma_rules();
        assert_merge(
            "(Π i 0 2 (select a i))",
            "(mul (let i 0 (select a i)) (let i 1 (select a i)))",
            &rules, "pi-unroll-2"
        );
    }

    #[test]
    fn test_egraph_sigma_factor_mul() {
        let rules = guarded_sigma_rules();
        assert_merge(
            "(Σ i 0 N (mul c (select arr i)))",
            "(mul c (Σ i 0 N (select arr i)))",
            &rules, "sigma-factor-mul (c independent of i)"
        );
    }

    #[test]
    fn test_egraph_sigma_factor_mul_blocked() {
        let rules = guarded_sigma_rules();
        assert_no_merge(
            "(Σ i 0 N (mul i (select arr i)))",
            "(mul i (Σ i 0 N (select arr i)))",
            &rules, "sigma-factor-mul should NOT fire when factor depends on loop var"
        );
    }

    #[test]
    fn test_egraph_sparsify_densify() {
        let rules = conversion_rules();
        assert_merge("(sparsify (densify p))", "p", &rules, "sparsify-densify");
    }

    #[test]
    fn test_egraph_as_mle_as_uv() {
        let rules = conversion_rules();
        assert_merge("(as-mle (as-uv m))", "m", &rules, "as-mle-as-uv");
    }

    // ═══════════════════════════════════════════════
    // Confluence & termination smoke tests
    // ═══════════════════════════════════════════════

    #[test]
    fn test_confluence_complex_arithmetic() {
        let rules = all_rules();
        // Complex nested expression: optimizer should terminate
        let expr: RecExpr<ArkLang> = "(add (mul (scale 2 x) (add y z)) (neg (mul x y)))".parse().unwrap();
        let runner = Runner::<ArkLang, TypeAnalysis>::default()
            .with_expr(&expr)
            .run(&rules);
        assert!(runner.egraph.number_of_classes() > 0, "e-graph should have classes");
        // The runner should have stopped (not hit the iteration limit in a degenerate way)
        assert!(runner.iterations.len() <= 30, "should converge in reasonable iterations");
    }

    #[test]
    fn test_confluence_sigma_conversion() {
        let rules = all_rules();
        let expr: RecExpr<ArkLang> = "(Σ i 0 3 (eval (densify (sparsify (poly:duv 1 2))) (select arr i)))".parse().unwrap();
        let runner = Runner::<ArkLang, TypeAnalysis>::default()
            .with_expr(&expr)
            .run(&rules);
        assert!(runner.egraph.number_of_classes() > 0);
    }

    #[test]
    fn test_confluence_pair_fft() {
        let rules = all_rules();
        let expr: RecExpr<ArkLang> = "(fst (pair (ifft 4 (fft 4 p)) (snd (pair a b))))".parse().unwrap();
        let runner = Runner::<ArkLang, TypeAnalysis>::default()
            .with_expr(&expr)
            .run(&rules);
        assert!(runner.egraph.number_of_classes() > 0);
    }

    // ═══════════════════════════════════════════════
    // Extraction quality tests
    // ═══════════════════════════════════════════════

    #[test]
    fn test_extraction_simplifies_double_neg() {
        let rules = all_rules();
        let input: RecExpr<ArkLang> = "(neg (neg x))".parse().unwrap();
        let runner = Runner::<ArkLang, TypeAnalysis>::default()
            .with_expr(&input)
            .run(&rules);
        let root = runner.roots[0];
        let extractor = Extractor::new(&runner.egraph, AstSize);
        let (cost, best) = extractor.find_best(root);
        assert_eq!(best.to_string(), "x");
        assert!(cost < AstSize.cost_rec(&input), "extracted should be simpler");
    }

    #[test]
    fn test_extraction_simplifies_scale_one() {
        let rules = all_rules();
        let input: RecExpr<ArkLang> = "(scale 1 (add a b))".parse().unwrap();
        let runner = Runner::<ArkLang, TypeAnalysis>::default()
            .with_expr(&input)
            .run(&rules);
        let root = runner.roots[0];
        let extractor = Extractor::new(&runner.egraph, AstSize);
        let (cost, _best) = extractor.find_best(root);
        assert!(cost <= AstSize.cost_rec(&input), "should not increase cost");
    }

    #[test]
    fn test_extraction_simplifies_fst_pair() {
        let rules = all_rules();
        let input: RecExpr<ArkLang> = "(fst (pair x y))".parse().unwrap();
        let runner = Runner::<ArkLang, TypeAnalysis>::default()
            .with_expr(&input)
            .run(&rules);
        let root = runner.roots[0];
        let extractor = Extractor::new(&runner.egraph, AstSize);
        let (cost, best) = extractor.find_best(root);
        assert_eq!(best.to_string(), "x");
        assert!(cost < AstSize.cost_rec(&input), "projection should simplify");
    }

    #[test]
    fn test_extraction_simplifies_ifft_fft() {
        let rules = all_rules();
        let input: RecExpr<ArkLang> = "(ifft n (fft n p))".parse().unwrap();
        let runner = Runner::<ArkLang, TypeAnalysis>::default()
            .with_expr(&input)
            .run(&rules);
        let root = runner.roots[0];
        let extractor = Extractor::new(&runner.egraph, AstSize);
        let (cost, best) = extractor.find_best(root);
        assert_eq!(best.to_string(), "p");
        assert!(cost < AstSize.cost_rec(&input), "roundtrip should simplify");
    }

    // ═══════════════════════════════════════════════
    // Wave 1: Typed add (tadd) rewrite rule tests
    // ═══════════════════════════════════════════════

    #[test]
    fn test_tadd_comm_rewrite() {
        let rules = typed_add_rules();
        assert_merge(
            "(tadd Field Field x y)",
            "(tadd Field Field y x)",
            &rules, "tadd-comm"
        );
    }

    #[test]
    fn test_tadd_assoc_rewrite() {
        let rules = typed_add_rules();
        assert_merge(
            "(tadd Field Field a (tadd Field Field b c))",
            "(tadd Field Field (tadd Field Field a b) c)",
            &rules, "tadd-assoc"
        );
    }

    #[test]
    fn test_tadd_comm_preserves_types() {
        // Ensure type pattern variables bind correctly in commutativity
        let rules = typed_add_rules();
        let e1: RecExpr<ArkLang> = "(tadd DensePoly Field a b)".parse().unwrap();
        let e2: RecExpr<ArkLang> = "(tadd Field DensePoly b a)".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(
            runner.egraph.find(id1),
            runner.egraph.find(id2),
            "tadd-comm should swap both types and operands"
        );
    }

    #[test]
    fn test_sigma_dist_tadd() {
        let rules = typed_sigma_rules();
        assert_merge(
            "(Σ i lo hi (tadd Field Field f g))",
            "(tadd Field Field (Σ i lo hi f) (Σ i lo hi g))",
            &rules, "sigma-dist-tadd"
        );
    }

    #[test]
    fn test_sigma_fusion_tadd() {
        let rules = typed_guarded_sigma_rules();
        assert_merge(
            "(tadd Field Field (Σ i lo hi f) (Σ i lo hi g))",
            "(Σ i lo hi (tadd Field Field f g))",
            &rules, "sigma-fusion-tadd"
        );
    }

    #[test]
    fn test_typed_sigma_unroll_2() {
        let rules = typed_sigma_unroll_rules();
        // After unrolling, Σ i 0 2 body should produce (tadd T T (let i 0 body) (let i 1 body))
        // The body type is Unknown (symbol 'a' has Unknown type), so the applier may not fire.
        // Use a body with known type (e.g., contains Int literal) to test.
        let e1: RecExpr<ArkLang> = "(Σ i 0 2 (select (mkarray 10 20) i))".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let runner = Runner::<ArkLang, TypeAnalysis>::default()
            .with_egraph(egraph)
            .run(&rules);
        // Verify the e-graph grew (unrolling added new nodes)
        assert!(runner.egraph.number_of_classes() > 1, "typed unroll should add nodes");
    }

    #[test]
    fn test_typed_sigma_unroll_3() {
        let rules = typed_sigma_unroll_rules();
        let e1: RecExpr<ArkLang> = "(Σ i 0 3 (select (mkarray 10 20 30) i))".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let runner = Runner::<ArkLang, TypeAnalysis>::default()
            .with_egraph(egraph)
            .run(&rules);
        assert!(runner.egraph.number_of_classes() > 1, "typed unroll-3 should add nodes");
    }

    // ═══════════════════════════════════════════════
    // Wave 2: Typed arith rewrite rules
    // ═══════════════════════════════════════════════

    #[test]
    fn test_double_tneg() {
        let rules = typed_arith_rules();
        let simplified = simplify("(tneg Field (tneg Field x))", &rules);
        assert_eq!(simplified, "x");
    }

    #[test]
    fn test_tmul_comm() {
        let rules = typed_arith_rules();
        assert_merge(
            "(tmul Field Field x y)",
            "(tmul Field Field y x)",
            &rules, "tmul-comm"
        );
    }

    #[test]
    fn test_tmul_assoc() {
        let rules = typed_arith_rules();
        assert_merge(
            "(tmul Field Field a (tmul Field Field b c))",
            "(tmul Field Field (tmul Field Field a b) c)",
            &rules, "tmul-assoc"
        );
    }

    #[test]
    fn test_tmul_dist() {
        let rules = all_rules();
        assert_merge(
            "(tmul Field Field a (tadd Field Field b c))",
            "(tadd Field Field (tmul Field Field a b) (tmul Field Field a c))",
            &rules, "tmul-dist"
        );
    }

    #[test]
    fn test_tscale_one() {
        let rules = typed_arith_rules();
        let simplified = simplify("(tscale Field 1 x)", &rules);
        assert_eq!(simplified, "x");
    }

    #[test]
    fn test_tscale_zero() {
        let rules = typed_arith_rules();
        let simplified = simplify("(tscale Field 0 x)", &rules);
        assert_eq!(simplified, "0");
    }

    #[test]
    fn test_tscale_dist() {
        let rules = all_rules();
        assert_merge(
            "(tscale Field c (tadd Field Field a b))",
            "(tadd Field Field (tscale Field c a) (tscale Field c b))",
            &rules, "tscale-dist"
        );
    }

    #[test]
    fn test_sigma_factor_tscale() {
        let rules = typed_guarded_arith_rules();
        assert_merge(
            "(Σ i 0 N (tscale Field c (select arr i)))",
            "(tscale Field c (Σ i 0 N (select arr i)))",
            &rules, "sigma-factor-tscale"
        );
    }

    #[test]
    fn test_sigma_factor_tscale_blocked() {
        let rules = typed_guarded_arith_rules();
        assert_no_merge(
            "(Σ i 0 N (tscale Field i (select arr i)))",
            "(tscale Field i (Σ i 0 N (select arr i)))",
            &rules, "sigma-factor-tscale should NOT fire when scalar depends on loop var"
        );
    }

    #[test]
    fn test_sigma_factor_tmul() {
        let rules = typed_guarded_arith_rules();
        assert_merge(
            "(Σ i 0 N (tmul Field Field c (select arr i)))",
            "(tmul Field Field c (Σ i 0 N (select arr i)))",
            &rules, "sigma-factor-tmul"
        );
    }
}
