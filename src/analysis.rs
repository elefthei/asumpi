// Egg Analysis for the arkΣΠ language.
//
// Tracks types and free variables per e-class, enabling
// guarded rewrites (e.g., factor extraction only when independent of loop var).

use egg::*;
use std::collections::HashSet;

use crate::language::ArkLang;
use crate::value::ArkType;

/// Per-e-class analysis data: possible types and free variables.
#[derive(Debug, Clone)]
pub struct TypeData {
    /// Possible types for this e-class (over-approximation after merging).
    pub types: HashSet<ArkType>,
    /// Free variables referenced by expressions in this e-class.
    pub free_vars: HashSet<Symbol>,
}

/// Type analysis for the arkΣΠ e-graph.
/// Computes types and free variables bottom-up.
#[derive(Default, Debug, Clone)]
pub struct TypeAnalysis;

/// Extract a Symbol from an e-class (if one exists).
pub(crate) fn get_bound_symbol(egraph: &EGraph<ArkLang, TypeAnalysis>, id: Id) -> Option<Symbol> {
    for node in &egraph[id].nodes {
        if let ArkLang::Symbol(s) = node {
            return Some(*s);
        }
    }
    None
}

impl Analysis<ArkLang> for TypeAnalysis {
    type Data = TypeData;

    fn make(egraph: &EGraph<ArkLang, Self>, enode: &ArkLang) -> TypeData {
        let cd = |id: &Id| -> &TypeData { &egraph[*id].data };
        let mut types = HashSet::new();
        let mut free_vars: HashSet<Symbol> = HashSet::new();

        match enode {
            ArkLang::Num(_) => {
                types.insert(ArkType::Int);
            }

            ArkLang::Symbol(s) => {
                types.insert(ArkType::Unknown);
                free_vars.insert(*s);
            }

            ArkLang::Ids(args) => {
                for id in args.iter() { free_vars.extend(&cd(id).free_vars); }
            }

            ArkLang::Poly(args) => {
                for id in args.iter() { free_vars.extend(&cd(id).free_vars); }
                // Could be SparseUVPoly (1 var) or MVPoly (>1 var)
                types.insert(ArkType::SparsePoly);
                types.insert(ArkType::MVPoly);
            }

            ArkLang::Fix([a, b, c]) => {
                free_vars.extend(&cd(a).free_vars);
                free_vars.extend(&cd(b).free_vars);
                free_vars.extend(&cd(c).free_vars);
                types.insert(ArkType::DenseMLE);
                types.insert(ArkType::SparseMLE);
            }

            ArkLang::Pair([a, b]) => {
                free_vars.extend(&cd(a).free_vars);
                free_vars.extend(&cd(b).free_vars);
                types.insert(ArkType::Pair);
            }

            ArkLang::Fst([a]) | ArkLang::Snd([a]) => {
                free_vars.extend(&cd(a).free_vars);
                types.insert(ArkType::Unknown);
            }

            ArkLang::Domain([a]) => {
                free_vars.extend(&cd(a).free_vars);
                types.insert(ArkType::Array);
            }

            ArkLang::Bound([a, b]) => {
                free_vars.extend(&cd(a).free_vars);
                free_vars.extend(&cd(b).free_vars);
                types.insert(ArkType::Int);
            }

            ArkLang::Sigma([idx, lo, hi, body]) | ArkLang::Pi([idx, lo, hi, body])
                | ArkLang::For([idx, lo, hi, body]) => {
                free_vars.extend(&cd(lo).free_vars);
                free_vars.extend(&cd(hi).free_vars);
                let mut body_vars = cd(body).free_vars.clone();
                if let Some(sym) = get_bound_symbol(egraph, *idx) {
                    body_vars.remove(&sym);
                }
                free_vars.extend(body_vars);
                types.extend(cd(body).types.iter().cloned());
            }

            ArkLang::MkArray(args) => {
                for id in args.iter() { free_vars.extend(&cd(id).free_vars); }
                types.insert(ArkType::Array);
            }

            ArkLang::Length([a]) => {
                free_vars.extend(&cd(a).free_vars);
                types.insert(ArkType::Int);
            }

            ArkLang::Let([name, val, body]) => {
                free_vars.extend(&cd(val).free_vars);
                let mut body_vars = cd(body).free_vars.clone();
                if let Some(sym) = get_bound_symbol(egraph, *name) {
                    body_vars.remove(&sym);
                }
                free_vars.extend(body_vars);
                types.extend(cd(body).types.iter().cloned());
            }

            ArkLang::If([cond, then_, else_]) => {
                free_vars.extend(&cd(cond).free_vars);
                free_vars.extend(&cd(then_).free_vars);
                free_vars.extend(&cd(else_).free_vars);
                types.extend(cd(then_).types.iter().cloned());
                types.extend(cd(else_).types.iter().cloned());
            }

            // ── Type Tags (leaf nodes, no children) ──
            ArkLang::TField | ArkLang::TCurve | ArkLang::TInt | ArkLang::TBool
            | ArkLang::TDensePoly | ArkLang::TSparsePoly | ArkLang::TDenseMLE
            | ArkLang::TSparseMLE | ArkLang::TMVPoly | ArkLang::TArray | ArkLang::TPair => {
                // Type tags carry no type information and no free vars
            }

            // ── Compound Type Tag ──
            ArkLang::ArrayOf([inner]) => {
                free_vars.extend(&cd(inner).free_vars);
                // ArrayOf is a type constructor — carries no runtime type
            }

            // ── Symbolic MLE Constructor (placeholder) ──
            ArkLang::Mle(args) => {
                for id in args.iter() { free_vars.extend(&cd(id).free_vars); }
                types.insert(ArkType::DenseMLE);
            }

            // ── Coerce ──
            ArkLang::Coerce([_src, dst, x]) => {
                free_vars.extend(&cd(x).free_vars);
                // Output type is determined by the destination type tag
                if let Some(ty) = crate::language::tag_to_type(&egraph[*dst].nodes[0]) {
                    types.insert(ty);
                } else {
                    types.insert(ArkType::Unknown);
                }
            }

            // ── Typed Add ──
            ArkLang::Add([_ta, _tb, a, b]) | ArkLang::Mul([_ta, _tb, a, b]) => {
                free_vars.extend(&cd(a).free_vars);
                free_vars.extend(&cd(b).free_vars);
                types.extend(cd(a).types.iter().cloned());
                types.extend(cd(b).types.iter().cloned());
            }

            // ── Typed Neg ──
            ArkLang::Neg([_t, a]) => {
                free_vars.extend(&cd(a).free_vars);
                types.extend(cd(a).types.iter().cloned());
            }

            // ── Typed Inv ──
            ArkLang::Inv([_t, a]) => {
                free_vars.extend(&cd(a).free_vars);
                types.insert(ArkType::Field);
            }

            // ── Typed Pow ──
            ArkLang::Pow([_t, base, exp]) => {
                free_vars.extend(&cd(base).free_vars);
                free_vars.extend(&cd(exp).free_vars);
                types.insert(ArkType::Field);
            }

            // ── Typed Eval ──
            ArkLang::Eval([_t, p, x]) => {
                free_vars.extend(&cd(p).free_vars);
                free_vars.extend(&cd(x).free_vars);
                types.insert(ArkType::Field);
            }

            // ── Typed Deg ──
            ArkLang::Deg([_t, p]) => {
                free_vars.extend(&cd(p).free_vars);
                types.insert(ArkType::Int);
            }

            // ── Typed NVars ──
            ArkLang::NVars([_t, p]) => {
                free_vars.extend(&cd(p).free_vars);
                types.insert(ArkType::Int);
            }

            // ── Typed Div ──
            ArkLang::Div([_t, a, b]) => {
                free_vars.extend(&cd(a).free_vars);
                free_vars.extend(&cd(b).free_vars);
                types.extend(cd(a).types.iter().cloned());
            }

            // ── Typed FFT ──
            ArkLang::Fft([_t, n, p]) => {
                free_vars.extend(&cd(n).free_vars);
                free_vars.extend(&cd(p).free_vars);
                types.insert(ArkType::Array);
            }

            // ── Typed IFFT ──
            ArkLang::Ifft([_t, n, evals]) => {
                free_vars.extend(&cd(n).free_vars);
                free_vars.extend(&cd(evals).free_vars);
                types.insert(ArkType::DensePoly);
            }

            // ── Typed Get ──
            ArkLang::Get([_t, arr, idx]) => {
                free_vars.extend(&cd(arr).free_vars);
                free_vars.extend(&cd(idx).free_vars);
                types.extend(cd(arr).types.iter().cloned()); // element type from the tag
            }

            // ── Typed Set ──
            ArkLang::Set([_t, arr, idx, val]) => {
                free_vars.extend(&cd(arr).free_vars);
                free_vars.extend(&cd(idx).free_vars);
                free_vars.extend(&cd(val).free_vars);
                types.insert(ArkType::Array);
            }

            // ── Typed Eq ──
            ArkLang::Eq([_t, a, b]) => {
                free_vars.extend(&cd(a).free_vars);
                free_vars.extend(&cd(b).free_vars);
                types.insert(ArkType::Bool);
            }

            // ── Sponge (Fiat-Shamir) ──
            ArkLang::TSponge => {
                // Type tag leaf — no type info, no free vars
            }

            ArkLang::AbsorbPublic([_t, sponge, val]) | ArkLang::AbsorbPrivate([_t, sponge, val]) => {
                free_vars.extend(&cd(sponge).free_vars);
                free_vars.extend(&cd(val).free_vars);
                types.insert(ArkType::Sponge);
            }

            ArkLang::Squeeze([_t, sponge]) => {
                free_vars.extend(&cd(sponge).free_vars);
                types.insert(ArkType::Pair);
            }
        }

        TypeData { types, free_vars }
    }

    fn merge(&mut self, a: &mut TypeData, b: TypeData) -> DidMerge {
        let ta = merge_set(&mut a.types, b.types);
        let va = merge_set(&mut a.free_vars, b.free_vars);
        // Conservative: report change on both sides if either grew
        DidMerge(ta || va, ta || va)
    }
}

fn merge_set<T: Eq + std::hash::Hash>(a: &mut HashSet<T>, b: HashSet<T>) -> bool {
    let old = a.len();
    a.extend(b);
    a.len() != old
}

/// Condition: expression `expr_var` does not reference the symbol bound by `idx_var`.
/// Used for guarded rewrites like factor extraction from Σ.
pub struct IndependentOf {
    pub expr_var: Var,
    pub idx_var: Var,
}

impl Condition<ArkLang, TypeAnalysis> for IndependentOf {
    fn check(
        &self,
        egraph: &mut EGraph<ArkLang, TypeAnalysis>,
        _eclass: Id,
        subst: &Subst,
    ) -> bool {
        let expr_id = subst[self.expr_var];
        let idx_id = subst[self.idx_var];
        if let Some(idx_sym) = get_bound_symbol(egraph, idx_id) {
            !egraph[expr_id].data.free_vars.contains(&idx_sym)
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_egraph(exprs: &[&str]) -> (EGraph<ArkLang, TypeAnalysis>, Vec<Id>) {
        let mut egraph = EGraph::default();
        let ids: Vec<Id> = exprs
            .iter()
            .map(|s| {
                let expr: RecExpr<ArkLang> = s.parse().unwrap();
                egraph.add_expr(&expr)
            })
            .collect();
        egraph.rebuild();
        (egraph, ids)
    }

    #[test]
    fn test_free_vars_simple() {
        let (egraph, ids) = make_egraph(&["(add Int Int x y)"]);
        let data = &egraph[ids[0]].data;
        assert!(data.free_vars.contains(&Symbol::from("x")));
        assert!(data.free_vars.contains(&Symbol::from("y")));
        assert_eq!(data.free_vars.len(), 2);
    }

    #[test]
    fn test_free_vars_constant() {
        let (egraph, ids) = make_egraph(&["(add Int Int 1 2)"]);
        let data = &egraph[ids[0]].data;
        assert!(data.free_vars.is_empty());
    }

    #[test]
    fn test_free_vars_let_binding() {
        let (egraph, ids) = make_egraph(&["(let x 5 (add Int Int x y))"]);
        let data = &egraph[ids[0]].data;
        // x is bound by let, only y is free
        assert!(!data.free_vars.contains(&Symbol::from("x")));
        assert!(data.free_vars.contains(&Symbol::from("y")));
        assert_eq!(data.free_vars.len(), 1);
    }

    #[test]
    fn test_free_vars_sigma() {
        let (egraph, ids) = make_egraph(&["(Σ i 0 N (mul Field Field c (get Int arr i)))"]);
        let data = &egraph[ids[0]].data;
        // i is bound by Σ; c, arr, N are free
        assert!(!data.free_vars.contains(&Symbol::from("i")));
        assert!(data.free_vars.contains(&Symbol::from("c")));
        assert!(data.free_vars.contains(&Symbol::from("arr")));
        assert!(data.free_vars.contains(&Symbol::from("N")));
        assert_eq!(data.free_vars.len(), 3);
    }

    #[test]
    fn test_free_vars_nested_sigma() {
        let (egraph, ids) = make_egraph(&["(Σ i 0 N (Σ j 0 M (mul Int Int i j)))"]);
        let data = &egraph[ids[0]].data;
        // i, j are bound; N, M are free
        assert!(!data.free_vars.contains(&Symbol::from("i")));
        assert!(!data.free_vars.contains(&Symbol::from("j")));
        assert!(data.free_vars.contains(&Symbol::from("N")));
        assert!(data.free_vars.contains(&Symbol::from("M")));
        assert_eq!(data.free_vars.len(), 2);
    }

    #[test]
    fn test_free_vars_let_val_references() {
        let (egraph, ids) = make_egraph(&["(let x (add Int Int y 1) (mul Int Int x z))"]);
        let data = &egraph[ids[0]].data;
        assert!(!data.free_vars.contains(&Symbol::from("x")));
        assert!(data.free_vars.contains(&Symbol::from("y")));
        assert!(data.free_vars.contains(&Symbol::from("z")));
        assert_eq!(data.free_vars.len(), 2);
    }

    #[test]
    fn test_type_int_literal() {
        let (egraph, ids) = make_egraph(&["42"]);
        let data = &egraph[ids[0]].data;
        assert!(data.types.contains(&ArkType::Int));
    }

    #[test]
    fn test_type_poly_constructor() {
        let (egraph, ids) = make_egraph(&["(coerce (arrayof Field) DensePoly (array 1 2 3))"]);
        let data = &egraph[ids[0]].data;
        assert!(data.types.contains(&ArkType::DensePoly));
    }

    #[test]
    fn test_type_eval_produces_field() {
        let (egraph, ids) = make_egraph(&["(eval DensePoly (coerce (arrayof Field) DensePoly (array 1 2)) 5)"]);
        let data = &egraph[ids[0]].data;
        assert!(data.types.contains(&ArkType::Field));
    }

    #[test]
    fn test_type_eq_produces_bool() {
        let (egraph, ids) = make_egraph(&["(eq Field x y)"]);
        let data = &egraph[ids[0]].data;
        assert!(data.types.contains(&ArkType::Bool));
    }

    #[test]
    fn test_type_mkarray() {
        let (egraph, ids) = make_egraph(&["(array 1 2 3)"]);
        let data = &egraph[ids[0]].data;
        assert!(data.types.contains(&ArkType::Array));
    }

    #[test]
    fn test_independent_of_true() {
        let (mut egraph, _) = make_egraph(&["(Σ i 0 3 (mul Field Field c (get Int arr i)))"]);
        let cond = IndependentOf {
            expr_var: "?c".parse().unwrap(),
            idx_var: "?i".parse().unwrap(),
        };
        let pat: Pattern<ArkLang> = "(Σ ?i ?lo ?hi (mul Field ?T ?c ?f))".parse().unwrap();
        let matches = pat.search(&egraph);
        assert!(!matches.is_empty(), "pattern should match");
        for mat in &matches {
            for subst in &mat.substs {
                assert!(
                    cond.check(&mut egraph, mat.eclass, subst),
                    "c should be independent of i"
                );
            }
        }
    }

    #[test]
    fn test_independent_of_false() {
        let (mut egraph, _) = make_egraph(&["(Σ i 0 3 (mul Field Field i (get Int arr i)))"]);
        let cond = IndependentOf {
            expr_var: "?c".parse().unwrap(),
            idx_var: "?i".parse().unwrap(),
        };
        let pat: Pattern<ArkLang> = "(Σ ?i ?lo ?hi (mul Field ?T ?c ?f))".parse().unwrap();
        let matches = pat.search(&egraph);
        assert!(!matches.is_empty(), "pattern should match");
        for mat in &matches {
            for subst in &mat.substs {
                assert!(
                    !cond.check(&mut egraph, mat.eclass, subst),
                    "i should NOT be independent of i"
                );
            }
        }
    }

    #[test]
    fn test_independent_of_complex_expr() {
        // c = (add Int Int a b), independent of i
        let (mut egraph, _) =
            make_egraph(&["(Σ i 0 N (mul Field Field (add Int Int a b) (get Int arr i)))"]);
        let cond = IndependentOf {
            expr_var: "?c".parse().unwrap(),
            idx_var: "?i".parse().unwrap(),
        };
        let pat: Pattern<ArkLang> = "(Σ ?i ?lo ?hi (mul Field ?T ?c ?f))".parse().unwrap();
        let matches = pat.search(&egraph);
        assert!(!matches.is_empty());
        for mat in &matches {
            for subst in &mat.substs {
                assert!(
                    cond.check(&mut egraph, mat.eclass, subst),
                    "(add Int Int a b) should be independent of i"
                );
            }
        }
    }

    #[test]
    fn test_independent_of_expr_uses_idx() {
        // c = (add Int Int a i), depends on i
        let (mut egraph, _) =
            make_egraph(&["(Σ i 0 N (mul Field Field (add Int Int a i) (get Int arr i)))"]);
        let cond = IndependentOf {
            expr_var: "?c".parse().unwrap(),
            idx_var: "?i".parse().unwrap(),
        };
        let pat: Pattern<ArkLang> = "(Σ ?i ?lo ?hi (mul Field ?T ?c ?f))".parse().unwrap();
        let matches = pat.search(&egraph);
        assert!(!matches.is_empty());
        for mat in &matches {
            for subst in &mat.substs {
                assert!(
                    !cond.check(&mut egraph, mat.eclass, subst),
                    "(add Int Int a i) should depend on i"
                );
            }
        }
    }
}
