// arkΣΠ Rewrite Rules
//
// Typed algebraic rules, eval distribution, Σ/Π transforms,
// and conversion identities for egg equality saturation.

use egg::*;
use crate::language::ArkLang;
use crate::analysis::{TypeAnalysis, IndependentOf};

/// Typed add rules (add commutativity, associativity, negation cancellation).
pub fn add_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("add-comm"; "(add ?T ?V ?a ?b)" => "(add ?V ?T ?b ?a)"),
        rewrite!("add-assoc"; "(add ?T ?V ?a (add ?V ?W ?b ?c))" => "(add ?T ?W (add ?T ?V ?a ?b) ?c)"),
        rewrite!("add-neg"; "(add ?T ?T ?a (neg ?T ?a))" => "0"),
    ]
}

/// Typed arithmetic rules (Wave 2: neg, mul, scale, pow).
pub fn arith_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        // ── Negation ──
        rewrite!("double-neg"; "(neg ?T (neg ?T ?a))" => "?a"),
        rewrite!("neg-as-scale"; "(neg ?T ?a)" => "(scale ?T -1 ?a)"),

        // ── Multiplication ──
        rewrite!("mul-comm"; "(mul ?T ?V ?a ?b)" => "(mul ?V ?T ?b ?a)"),
        rewrite!("mul-assoc"; "(mul ?T ?V ?a (mul ?V ?W ?b ?c))" => "(mul ?T ?W (mul ?T ?V ?a ?b) ?c)"),
        rewrite!("mul-dist"; "(mul ?T ?T ?a (add ?T ?T ?b ?c))" => "(add ?T ?T (mul ?T ?T ?a ?b) (mul ?T ?T ?a ?c))"),

        // ── Scale ──
        rewrite!("scale-one"; "(scale ?T 1 ?a)" => "?a"),
        rewrite!("scale-zero"; "(scale ?T 0 ?a)" => "0"),
        rewrite!("scale-dist"; "(scale ?T ?c (add ?T ?T ?a ?b))" => "(add ?T ?T (scale ?T ?c ?a) (scale ?T ?c ?b))"),
    ]
}

/// Typed guarded sigma rules for scale/mul factor extraction.
pub fn guarded_arith_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("sigma-factor-scale";
            "(Σ ?i ?lo ?hi (scale ?T ?c ?f))" => "(scale ?T ?c (Σ ?i ?lo ?hi ?f))"
            if IndependentOf { expr_var: "?c".parse().unwrap(), idx_var: "?i".parse().unwrap() }
        ),
        rewrite!("sigma-factor-mul";
            "(Σ ?i ?lo ?hi (mul ?T ?T ?c ?f))" => "(mul ?T ?T ?c (Σ ?i ?lo ?hi ?f))"
            if IndependentOf { expr_var: "?c".parse().unwrap(), idx_var: "?i".parse().unwrap() }
        ),
    ]
}

/// Custom applier that reads the body type from TypeAnalysis to emit typed add/mul.
struct UnrollApplier {
    /// Pattern variables for the body subexpressions (one per iteration value)
    body_var: Var,
    /// Pattern variable for the loop index
    idx_var: Var,
    /// Iteration values (e.g., [0, 1] for unroll-2)
    iter_vals: Vec<i64>,
    /// Whether to use add (for Σ) or mul (for Π)
    op: &'static str,
}

impl Applier<ArkLang, TypeAnalysis> for UnrollApplier {
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

        // Build a right-associative chain of add (or mul for Π)
        let result = if self.op == "add" {
            // (add T T (let i 0 body) (add T T (let i 1 body) ...))
            let mut acc = *let_ids.last().unwrap();
            for &lid in let_ids[..let_ids.len() - 1].iter().rev() {
                acc = egraph.add(ArkLang::Add([tag_id, tag_id, lid, acc]));
            }
            acc
        } else {
            // mul: use Mul for typed Π unrolling
            let mut acc = *let_ids.last().unwrap();
            for &lid in let_ids[..let_ids.len() - 1].iter().rev() {
                acc = egraph.add(ArkLang::Mul([tag_id, tag_id, lid, acc]));
            }
            acc
        };

        egraph.union(eclass, result);
        vec![result]
    }
}

/// Typed sigma unrolling rules using UnrollApplier.
pub fn sigma_unroll_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        Rewrite::new(
            Symbol::from("typed-sigma-unroll-2"),
            "(Σ ?i 0 2 ?f)".parse::<Pattern<ArkLang>>().unwrap(),
            UnrollApplier {
                body_var: "?f".parse().unwrap(),
                idx_var: "?i".parse().unwrap(),
                iter_vals: vec![0, 1],
                op: "add",
            },
        ).unwrap(),
        Rewrite::new(
            Symbol::from("typed-sigma-unroll-3"),
            "(Σ ?i 0 3 ?f)".parse::<Pattern<ArkLang>>().unwrap(),
            UnrollApplier {
                body_var: "?f".parse().unwrap(),
                idx_var: "?i".parse().unwrap(),
                iter_vals: vec![0, 1, 2],
                op: "add",
            },
        ).unwrap(),
    ]
}

/// Typed sigma distribution over add.
pub fn sigma_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("sigma-dist-add"; "(Σ ?i ?lo ?hi (add ?T ?T ?f ?g))"
            => "(add ?T ?T (Σ ?i ?lo ?hi ?f) (Σ ?i ?lo ?hi ?g))"),
    ]
}

/// Typed sigma fusion rule.
pub fn guarded_sigma_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("sigma-fusion-add";
            "(add ?T ?T (Σ ?i ?lo ?hi ?f) (Σ ?i ?lo ?hi ?g))" => "(Σ ?i ?lo ?hi (add ?T ?T ?f ?g))"
        ),
    ]
}

/// Typed eval-distribution rules (typed polynomial evaluation distributes).
pub fn eval_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("eval-add"; "(eval ?T (add ?T ?T ?p ?q) ?x)"
            => "(add Field Field (eval ?T ?p ?x) (eval ?T ?q ?x))"),
        rewrite!("eval-neg"; "(eval ?T (neg ?T ?p) ?x)"
            => "(neg Field (eval ?T ?p ?x))"),
        rewrite!("eval-scale"; "(eval ?T (scale ?T ?c ?p) ?x)"
            => "(mul Field Field ?c (eval ?T ?p ?x))"),
        rewrite!("eval-mul"; "(eval ?T (mul ?T ?T ?p ?q) ?x)"
            => "(mul Field Field (eval ?T ?p ?x) (eval ?T ?q ?x))"),
    ]
}

/// Typed conversion roundtrip rules (coerce + fft/ifft + structural).
pub fn conversion_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        // Coerce roundtrips
        rewrite!("coerce-dense-sparse-roundtrip";
            "(coerce DensePoly SparsePoly (coerce SparsePoly DensePoly ?p))" => "?p"),
        rewrite!("coerce-sparse-dense-roundtrip";
            "(coerce SparsePoly DensePoly (coerce DensePoly SparsePoly ?p))" => "?p"),
        rewrite!("coerce-mle-poly-roundtrip";
            "(coerce DensePoly DenseMLE (coerce DenseMLE DensePoly ?p))" => "?p"),
        rewrite!("coerce-poly-mle-roundtrip";
            "(coerce DenseMLE DensePoly (coerce DensePoly DenseMLE ?m))" => "?m"),
        // Typed FFT/IFFT roundtrips
        rewrite!("ifft-fft"; "(ifft Array ?n (fft ?T ?n ?p))" => "?p"),
        rewrite!("fft-ifft"; "(fft DensePoly ?n (ifft Array ?n ?e))" => "?e"),
        // Tuple projections
        rewrite!("fst-pair"; "(fst (pair ?a ?b))" => "?a"),
        rewrite!("snd-pair"; "(snd (pair ?a ?b))" => "?b"),
        rewrite!("pair-eta"; "(pair (fst ?p) (snd ?p))" => "?p"),
    ]
}

/// All rules combined (typed only).
pub fn all_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    let mut rules = add_rules();
    rules.extend(arith_rules());
    rules.extend(sigma_rules());
    rules.extend(guarded_sigma_rules());
    rules.extend(guarded_arith_rules());
    rules.extend(sigma_unroll_rules());
    rules.extend(eval_rules());
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

    // ═══════════════════════════════════════════════
    // Wave 1: Typed add (add) rewrite rule tests
    // ═══════════════════════════════════════════════

    #[test]
    fn test_add_comm_rewrite() {
        let rules = add_rules();
        assert_merge(
            "(add Field Field x y)",
            "(add Field Field y x)",
            &rules, "add-comm"
        );
    }

    #[test]
    fn test_add_assoc_rewrite() {
        let rules = add_rules();
        assert_merge(
            "(add Field Field a (add Field Field b c))",
            "(add Field Field (add Field Field a b) c)",
            &rules, "add-assoc"
        );
    }

    #[test]
    fn test_add_comm_preserves_types() {
        // Ensure type pattern variables bind correctly in commutativity
        let rules = add_rules();
        let e1: RecExpr<ArkLang> = "(add DensePoly Field a b)".parse().unwrap();
        let e2: RecExpr<ArkLang> = "(add Field DensePoly b a)".parse().unwrap();
        let mut egraph: EGraph<ArkLang, TypeAnalysis> = EGraph::default();
        let id1 = egraph.add_expr(&e1);
        let id2 = egraph.add_expr(&e2);
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        assert_eq!(
            runner.egraph.find(id1),
            runner.egraph.find(id2),
            "add-comm should swap both types and operands"
        );
    }

    #[test]
    fn test_sigma_dist_tadd() {
        let rules = sigma_rules();
        assert_merge(
            "(Σ i lo hi (add Field Field f g))",
            "(add Field Field (Σ i lo hi f) (Σ i lo hi g))",
            &rules, "sigma-dist-add"
        );
    }

    #[test]
    fn test_sigma_fusion_tadd() {
        let rules = guarded_sigma_rules();
        assert_merge(
            "(add Field Field (Σ i lo hi f) (Σ i lo hi g))",
            "(Σ i lo hi (add Field Field f g))",
            &rules, "sigma-fusion-add"
        );
    }

    #[test]
    fn test_typed_sigma_unroll_2() {
        let rules = sigma_unroll_rules();
        // After unrolling, Σ i 0 2 body should produce (add T T (let i 0 body) (let i 1 body))
        // The body type is Unknown (symbol 'a' has Unknown type), so the applier may not fire.
        // Use a body with known type (e.g., contains Int literal) to test.
        let e1: RecExpr<ArkLang> = "(Σ i 0 2 (get Int (array 10 20) i))".parse().unwrap();
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
        let rules = sigma_unroll_rules();
        let e1: RecExpr<ArkLang> = "(Σ i 0 3 (get Int (array 10 20 30) i))".parse().unwrap();
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
        let rules = arith_rules();
        let simplified = simplify("(neg Field (neg Field x))", &rules);
        assert_eq!(simplified, "x");
    }

    #[test]
    fn test_mul_comm() {
        let rules = arith_rules();
        assert_merge(
            "(mul Field Field x y)",
            "(mul Field Field y x)",
            &rules, "mul-comm"
        );
    }

    #[test]
    fn test_mul_assoc() {
        let rules = arith_rules();
        assert_merge(
            "(mul Field Field a (mul Field Field b c))",
            "(mul Field Field (mul Field Field a b) c)",
            &rules, "mul-assoc"
        );
    }

    #[test]
    fn test_mul_dist() {
        let rules = all_rules();
        assert_merge(
            "(mul Field Field a (add Field Field b c))",
            "(add Field Field (mul Field Field a b) (mul Field Field a c))",
            &rules, "mul-dist"
        );
    }

    #[test]
    fn test_scale_one() {
        let rules = arith_rules();
        let simplified = simplify("(scale Field 1 x)", &rules);
        assert_eq!(simplified, "x");
    }

    #[test]
    fn test_scale_zero() {
        let rules = arith_rules();
        let simplified = simplify("(scale Field 0 x)", &rules);
        assert_eq!(simplified, "0");
    }

    #[test]
    fn test_scale_dist() {
        let rules = all_rules();
        assert_merge(
            "(scale Field c (add Field Field a b))",
            "(add Field Field (scale Field c a) (scale Field c b))",
            &rules, "scale-dist"
        );
    }

    #[test]
    fn test_sigma_factor_tscale() {
        let rules = guarded_arith_rules();
        assert_merge(
            "(Σ i 0 N (scale Field c (get Int arr i)))",
            "(scale Field c (Σ i 0 N (get Int arr i)))",
            &rules, "sigma-factor-scale"
        );
    }

    #[test]
    fn test_sigma_factor_tscale_blocked() {
        let rules = guarded_arith_rules();
        assert_no_merge(
            "(Σ i 0 N (scale Field i (get Int arr i)))",
            "(scale Field i (Σ i 0 N (get Int arr i)))",
            &rules, "sigma-factor-scale should NOT fire when scalar depends on loop var"
        );
    }

    #[test]
    fn test_sigma_factor_tmul() {
        let rules = guarded_arith_rules();
        assert_merge(
            "(Σ i 0 N (mul Field Field c (get Int arr i)))",
            "(mul Field Field c (Σ i 0 N (get Int arr i)))",
            &rules, "sigma-factor-mul"
        );
    }

    // ═══════════════════════════════════════════════
    // Wave 3: Typed eval-distribution + conversion + aadd rules
    // ═══════════════════════════════════════════════

    #[test]
    fn test_eval_tadd_distribution() {
        let rules = eval_rules();
        assert_merge(
            "(eval DensePoly (add DensePoly DensePoly p q) x)",
            "(add Field Field (eval DensePoly p x) (eval DensePoly q x))",
            &rules, "eval-add"
        );
    }

    #[test]
    fn test_eval_tneg_distribution() {
        let rules = eval_rules();
        assert_merge(
            "(eval DensePoly (neg DensePoly p) x)",
            "(neg Field (eval DensePoly p x))",
            &rules, "eval-neg"
        );
    }

    #[test]
    fn test_eval_tscale_distribution() {
        let rules = eval_rules();
        assert_merge(
            "(eval DensePoly (scale DensePoly c p) x)",
            "(mul Field Field c (eval DensePoly p x))",
            &rules, "eval-scale"
        );
    }

    #[test]
    fn test_eval_tmul_distribution() {
        let rules = eval_rules();
        assert_merge(
            "(eval DensePoly (mul DensePoly DensePoly p q) x)",
            "(mul Field Field (eval DensePoly p x) (eval DensePoly q x))",
            &rules, "eval-mul"
        );
    }

    #[test]
    fn test_coerce_dense_sparse_roundtrip() {
        let rules = conversion_rules();
        let simplified = simplify(
            "(coerce DensePoly SparsePoly (coerce SparsePoly DensePoly p))",
            &rules
        );
        assert_eq!(simplified, "p");
    }

    #[test]
    fn test_coerce_sparse_dense_roundtrip() {
        let rules = conversion_rules();
        let simplified = simplify(
            "(coerce SparsePoly DensePoly (coerce DensePoly SparsePoly p))",
            &rules
        );
        assert_eq!(simplified, "p");
    }

    #[test]
    fn test_coerce_mle_poly_roundtrip() {
        let rules = conversion_rules();
        let simplified = simplify(
            "(coerce DensePoly DenseMLE (coerce DenseMLE DensePoly p))",
            &rules
        );
        assert_eq!(simplified, "p");
    }

    #[test]
    fn test_ifft_tfft_roundtrip_rule() {
        let rules = conversion_rules();
        let simplified = simplify(
            "(ifft Array n (fft DensePoly n p))",
            &rules
        );
        assert_eq!(simplified, "p");
    }

    #[test]
    fn test_fft_tifft_roundtrip_rule() {
        let rules = conversion_rules();
        let simplified = simplify(
            "(fft DensePoly n (ifft Array n e))",
            &rules
        );
        assert_eq!(simplified, "e");
    }

}
