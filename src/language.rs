// arkΣΠ Language Definition
//
// A unified sum-of-products language with 43 nodes.
// Generic arithmetic, indexed Σ/Π, explicit conversions.

use egg::*;

define_language! {
    /// arkΣΠ: Unified algebraic language with generic operations.
    ///
    /// All arithmetic is generic (add works on Fr, G1, Poly, etc).
    /// Indexed Σ/Π with symbolic bounded sizes for staged computation.
    /// Explicit conversion operators for representation/domain changes.
    pub enum ArkLang {
        Num(i64),

        // ── Generic Arithmetic (6) ──
        "add"   = Add([Id; 2]),
        "neg"   = Neg([Id; 1]),
        "mul"   = Mul([Id; 2]),
        "inv"   = Inv([Id; 1]),
        "scale" = Scale([Id; 2]),
        "pow"   = Pow([Id; 2]),

        // ── Evaluation & Queries (3) ──
        "eval"  = Eval([Id; 2]),
        "deg"   = Deg([Id; 1]),
        "nvars" = NVars([Id; 1]),

        // ── Polynomial Constructors (5 + 2 symbolic) ──
        "poly:duv"  = PolyDUV(Box<[Id]>),
        "poly:suv"  = PolySUV(Box<[Id]>),
        "poly:dmle" = PolyDMLE([Id; 2]),
        "poly:smle" = PolySMLE([Id; 2]),
        "poly:mv"   = PolyMV([Id; 3]),
        "ids"       = Ids(Box<[Id]>),
        "poly"      = Poly(Box<[Id]>),

        // ── Poly-Specific (2) ──
        "pdiv" = PDiv([Id; 2]),
        "fix"  = Fix([Id; 2]),

        // ── Tuples (3) ──
        "pair" = Pair([Id; 2]),
        "fst"  = Fst([Id; 1]),
        "snd"  = Snd([Id; 1]),

        // ── FFT / Domain (3) ──
        "domain" = Domain([Id; 1]),
        "fft"    = Fft([Id; 2]),
        "ifft"   = Ifft([Id; 2]),

        // ── Indexed Sum/Product (3) ──
        "bound" = Bound([Id; 2]),
        "Σ"     = Sigma([Id; 4]),
        "Π"     = Pi([Id; 4]),

        // ── Conversions (4) ──
        "densify"  = Densify([Id; 1]),
        "sparsify" = Sparsify([Id; 1]),
        "as-uv"    = AsUV([Id; 1]),
        "as-mle"   = AsMLE([Id; 1]),

        // ── Array (5) ──
        "mkarray" = MkArray(Box<[Id]>),
        "select"  = Select([Id; 2]),
        "store"   = Store([Id; 3]),
        "alen"    = ALen([Id; 1]),
        "aadd"    = AAdd([Id; 2]),

        // ── Control (2) ──
        "let" = Let([Id; 3]),
        "if"  = If([Id; 3]),

        // ── Comparison (1) ──
        "eq" = Eq([Id; 2]),

        // ── Type Tags (leaf nodes for explicit typing) ──
        // Must be before Symbol so the parser matches them first.
        "Field"      = TField,
        "Curve"      = TCurve,
        "Int"        = TInt,
        "Bool"       = TBool,
        "DensePoly"  = TDensePoly,
        "SparsePoly" = TSparsePoly,
        "DenseMLE"   = TDenseMLE,
        "SparseMLE"  = TSparseMLE,
        "MVPoly"     = TMVPoly,
        "Array"      = TArray,
        "Pair"       = TPair,

        // ── Typed Operations (coexist with untyped during migration) ──
        "coerce" = Coerce([Id; 3]),
        "tadd"   = TAdd([Id; 4]),
        "tneg"   = TNeg([Id; 2]),
        "tmul"   = TMul([Id; 4]),
        "tinv"   = TInv([Id; 2]),
        "tscale" = TScale([Id; 3]),
        "tpow"   = TPow([Id; 3]),
        "teval"  = TEval([Id; 3]),
        "tdeg"   = TDeg([Id; 2]),
        "tnvars" = TNVars([Id; 2]),
        "tpdiv"  = TPDiv([Id; 3]),
        "tfft"   = TFft([Id; 3]),
        "tifft"  = TIfft([Id; 3]),
        "tselect"= TSelect([Id; 3]),
        "tstore" = TStore([Id; 4]),
        "taadd"  = TAAdd([Id; 3]),
        "teq"    = TEq([Id; 3]),

        // ── Variable Reference ──
        Symbol(egg::Symbol),
    }
}

use crate::value::ArkType;

/// Convert a type-tag AST node to its corresponding ArkType.
pub fn tag_to_type(node: &ArkLang) -> Option<ArkType> {
    match node {
        ArkLang::TField     => Some(ArkType::Field),
        ArkLang::TCurve     => Some(ArkType::Curve),
        ArkLang::TInt       => Some(ArkType::Int),
        ArkLang::TBool      => Some(ArkType::Bool),
        ArkLang::TDensePoly => Some(ArkType::DensePoly),
        ArkLang::TSparsePoly=> Some(ArkType::SparsePoly),
        ArkLang::TDenseMLE  => Some(ArkType::DenseMLE),
        ArkLang::TSparseMLE => Some(ArkType::SparseMLE),
        ArkLang::TMVPoly    => Some(ArkType::MVPoly),
        ArkLang::TArray     => Some(ArkType::Array),
        ArkLang::TPair      => Some(ArkType::Pair),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple() {
        let expr: RecExpr<ArkLang> = "(add 1 2)".parse().unwrap();
        assert_eq!(expr.as_ref().len(), 3);
    }

    #[test]
    fn test_parse_nested() {
        let expr: RecExpr<ArkLang> = "(mul (add x y) z)".parse().unwrap();
        assert!(expr.as_ref().len() >= 4);
    }

    #[test]
    fn test_parse_variable() {
        let expr: RecExpr<ArkLang> = "x".parse().unwrap();
        assert_eq!(expr.as_ref().len(), 1);
        match &expr.as_ref()[0] {
            ArkLang::Symbol(s) => assert_eq!(s.as_str(), "x"),
            _ => panic!("expected Symbol"),
        }
    }

    #[test]
    fn test_parse_array() {
        let expr: RecExpr<ArkLang> = "(mkarray 1 2 3)".parse().unwrap();
        assert_eq!(expr.as_ref().len(), 4);
    }

    #[test]
    fn test_parse_sigma() {
        let expr: RecExpr<ArkLang> =
            "(Σ i 0 3 (select (mkarray 10 20 30) i))".parse().unwrap();
        assert!(expr.as_ref().len() >= 4);
    }

    #[test]
    fn test_parse_let() {
        let expr: RecExpr<ArkLang> =
            "(let x 42 (add x x))".parse().unwrap();
        assert!(expr.as_ref().len() >= 4);
    }

    #[test]
    fn test_parse_poly() {
        let expr: RecExpr<ArkLang> =
            "(eval (poly:duv 1 2 3) 5)".parse().unwrap();
        assert!(expr.as_ref().len() >= 5);
    }

    #[test]
    fn test_roundtrip_display_parse() {
        let expr: RecExpr<ArkLang> = "(add (mul 3 x) (neg y))".parse().unwrap();
        let s = expr.to_string();
        let expr2: RecExpr<ArkLang> = s.parse().unwrap();
        assert_eq!(expr, expr2);
    }
}
