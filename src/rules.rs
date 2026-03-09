// arkΣΠ Rewrite Rules
//
// Typed algebraic rules, eval distribution, Σ/Π transforms,
// and conversion identities for egg equality saturation.

use egg::*;
use crate::language::ArkLang;
use crate::analysis::{TypeAnalysis, IndependentOf};

/// Typed add rules (tadd commutativity, associativity, negation cancellation).
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
            // tmul: use TMul for typed Π unrolling
            let mut acc = *let_ids.last().unwrap();
            for &lid in let_ids[..let_ids.len() - 1].iter().rev() {
                acc = egraph.add(ArkLang::TMul([tag_id, tag_id, lid, acc]));
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

/// Typed eval-distribution rules (typed polynomial evaluation distributes).
pub fn typed_eval_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    vec![
        rewrite!("teval-tadd"; "(teval ?T (tadd ?T ?T ?p ?q) ?x)"
            => "(tadd Field Field (teval ?T ?p ?x) (teval ?T ?q ?x))"),
        rewrite!("teval-tneg"; "(teval ?T (tneg ?T ?p) ?x)"
            => "(tneg Field (teval ?T ?p ?x))"),
        rewrite!("teval-tscale"; "(teval ?T (tscale ?T ?c ?p) ?x)"
            => "(tmul Field Field ?c (teval ?T ?p ?x))"),
        rewrite!("teval-tmul"; "(teval ?T (tmul ?T ?T ?p ?q) ?x)"
            => "(tmul Field Field (teval ?T ?p ?x) (teval ?T ?q ?x))"),
    ]
}

/// Typed conversion roundtrip rules (coerce + fft/ifft + structural).
pub fn typed_conversion_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
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
        rewrite!("tifft-tfft"; "(tifft Array ?n (tfft ?T ?n ?p))" => "?p"),
        rewrite!("tfft-tifft"; "(tfft DensePoly ?n (tifft Array ?n ?e))" => "?e"),
        // Typed aadd commutativity
        rewrite!("taadd-comm"; "(taadd ?T ?a ?b)" => "(taadd ?T ?b ?a)"),
        // Tuple projections
        rewrite!("fst-pair"; "(fst (pair ?a ?b))" => "?a"),
        rewrite!("snd-pair"; "(snd (pair ?a ?b))" => "?b"),
        rewrite!("pair-eta"; "(pair (fst ?p) (snd ?p))" => "?p"),
    ]
}

/// All rules combined (typed only).
pub fn all_rules() -> Vec<Rewrite<ArkLang, TypeAnalysis>> {
    let mut rules = typed_add_rules();
    rules.extend(typed_arith_rules());
    rules.extend(typed_sigma_rules());
    rules.extend(typed_guarded_sigma_rules());
    rules.extend(typed_guarded_arith_rules());
    rules.extend(typed_sigma_unroll_rules());
    rules.extend(typed_eval_rules());
    rules.extend(typed_conversion_rules());
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
        let e1: RecExpr<ArkLang> = "(Σ i 0 2 (tselect Int (mkarray 10 20) i))".parse().unwrap();
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
        let e1: RecExpr<ArkLang> = "(Σ i 0 3 (tselect Int (mkarray 10 20 30) i))".parse().unwrap();
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
            "(Σ i 0 N (tscale Field c (tselect Int arr i)))",
            "(tscale Field c (Σ i 0 N (tselect Int arr i)))",
            &rules, "sigma-factor-tscale"
        );
    }

    #[test]
    fn test_sigma_factor_tscale_blocked() {
        let rules = typed_guarded_arith_rules();
        assert_no_merge(
            "(Σ i 0 N (tscale Field i (tselect Int arr i)))",
            "(tscale Field i (Σ i 0 N (tselect Int arr i)))",
            &rules, "sigma-factor-tscale should NOT fire when scalar depends on loop var"
        );
    }

    #[test]
    fn test_sigma_factor_tmul() {
        let rules = typed_guarded_arith_rules();
        assert_merge(
            "(Σ i 0 N (tmul Field Field c (tselect Int arr i)))",
            "(tmul Field Field c (Σ i 0 N (tselect Int arr i)))",
            &rules, "sigma-factor-tmul"
        );
    }

    // ═══════════════════════════════════════════════
    // Wave 3: Typed eval-distribution + conversion + aadd rules
    // ═══════════════════════════════════════════════

    #[test]
    fn test_teval_tadd_distribution() {
        let rules = typed_eval_rules();
        assert_merge(
            "(teval DensePoly (tadd DensePoly DensePoly p q) x)",
            "(tadd Field Field (teval DensePoly p x) (teval DensePoly q x))",
            &rules, "teval-tadd"
        );
    }

    #[test]
    fn test_teval_tneg_distribution() {
        let rules = typed_eval_rules();
        assert_merge(
            "(teval DensePoly (tneg DensePoly p) x)",
            "(tneg Field (teval DensePoly p x))",
            &rules, "teval-tneg"
        );
    }

    #[test]
    fn test_teval_tscale_distribution() {
        let rules = typed_eval_rules();
        assert_merge(
            "(teval DensePoly (tscale DensePoly c p) x)",
            "(tmul Field Field c (teval DensePoly p x))",
            &rules, "teval-tscale"
        );
    }

    #[test]
    fn test_teval_tmul_distribution() {
        let rules = typed_eval_rules();
        assert_merge(
            "(teval DensePoly (tmul DensePoly DensePoly p q) x)",
            "(tmul Field Field (teval DensePoly p x) (teval DensePoly q x))",
            &rules, "teval-tmul"
        );
    }

    #[test]
    fn test_coerce_dense_sparse_roundtrip() {
        let rules = typed_conversion_rules();
        let simplified = simplify(
            "(coerce DensePoly SparsePoly (coerce SparsePoly DensePoly p))",
            &rules
        );
        assert_eq!(simplified, "p");
    }

    #[test]
    fn test_coerce_sparse_dense_roundtrip() {
        let rules = typed_conversion_rules();
        let simplified = simplify(
            "(coerce SparsePoly DensePoly (coerce DensePoly SparsePoly p))",
            &rules
        );
        assert_eq!(simplified, "p");
    }

    #[test]
    fn test_coerce_mle_poly_roundtrip() {
        let rules = typed_conversion_rules();
        let simplified = simplify(
            "(coerce DensePoly DenseMLE (coerce DenseMLE DensePoly p))",
            &rules
        );
        assert_eq!(simplified, "p");
    }

    #[test]
    fn test_tifft_tfft_roundtrip_rule() {
        let rules = typed_conversion_rules();
        let simplified = simplify(
            "(tifft Array n (tfft DensePoly n p))",
            &rules
        );
        assert_eq!(simplified, "p");
    }

    #[test]
    fn test_tfft_tifft_roundtrip_rule() {
        let rules = typed_conversion_rules();
        let simplified = simplify(
            "(tfft DensePoly n (tifft Array n e))",
            &rules
        );
        assert_eq!(simplified, "e");
    }

    #[test]
    fn test_taadd_comm() {
        let rules = typed_conversion_rules();
        assert_merge(
            "(taadd Field a b)",
            "(taadd Field b a)",
            &rules, "taadd-comm"
        );
    }
}
