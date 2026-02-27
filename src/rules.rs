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

/// All rules combined.
pub fn all_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    let mut rules = algebra_rules();
    rules.extend(eval_rules());
    rules.extend(sigma_rules());
    rules.extend(guarded_sigma_rules());
    rules.extend(conversion_rules());
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
}
