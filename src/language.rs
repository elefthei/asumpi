// arkΣΠ Language Definition
//
// A typed algebraic IR with typed arithmetic, indexed Σ/Π,
// polynomial constructors, and explicit coercions.

use egg::*;

define_language! {
    /// arkΣΠ: Typed algebraic language.
    ///
    /// All arithmetic is typed (add, mul, etc. carry type tags).
    /// Indexed Σ/Π with symbolic bounded sizes for staged computation.
    /// Explicit coerce operator for representation/domain changes.
    pub enum ArkLang {
        Num(i64),

        // ── Symbolic Constructors ──
        "ids"       = Ids(Box<[Id]>),
        "poly"      = Poly(Box<[Id]>),
        "mle"       = Mle(Box<[Id]>),

        // ── Poly-Specific ──
        "fix"  = Fix([Id; 3]),

        // ── Tuples ──
        "pair" = Pair([Id; 2]),
        "fst"  = Fst([Id; 1]),
        "snd"  = Snd([Id; 1]),

        // ── Domain ──
        "domain" = Domain([Id; 1]),

        // ── Indexed Sum/Product/Comprehension ──
        "bound" = Bound([Id; 2]),
        "Σ"     = Sigma([Id; 4]),
        "Π"     = Pi([Id; 4]),
        "for"   = For([Id; 4]),

        // ── Array ──
        "array" = MkArray(Box<[Id]>),
        "length" = Length([Id; 1]),

        // ── Control ──
        "let" = Let([Id; 3]),
        "if"  = If([Id; 3]),

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

        // ── Compound Type Tag ──
        "arrayof" = ArrayOf([Id; 1]),

        // ── Typed Operations ──
        "coerce"  = Coerce([Id; 3]),
        "add"     = Add([Id; 4]),
        "neg"     = Neg([Id; 2]),
        "mul"     = Mul([Id; 4]),
        "inv"     = Inv([Id; 2]),
        "pow"     = Pow([Id; 3]),
        "eval"    = Eval([Id; 3]),
        "deg"     = Deg([Id; 2]),
        "numvars" = NVars([Id; 2]),
        "div"     = Div([Id; 3]),
        "fft"     = Fft([Id; 3]),
        "ifft"    = Ifft([Id; 3]),
        "get"     = Get([Id; 3]),
        "set"     = Set([Id; 4]),
        "eq"      = Eq([Id; 3]),

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
        let expr: RecExpr<ArkLang> = "(add Int Int 1 2)".parse().unwrap();
        assert_eq!(expr.as_ref().len(), 5);
    }

    #[test]
    fn test_parse_nested() {
        let expr: RecExpr<ArkLang> = "(mul Int Int (add Int Int x y) z)".parse().unwrap();
        assert!(expr.as_ref().len() >= 6);
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
        let expr: RecExpr<ArkLang> = "(array 1 2 3)".parse().unwrap();
        assert_eq!(expr.as_ref().len(), 4);
    }

    #[test]
    fn test_parse_sigma() {
        let expr: RecExpr<ArkLang> =
            "(Σ i 0 3 (get Int (array 10 20 30) i))".parse().unwrap();
        assert!(expr.as_ref().len() >= 4);
    }

    #[test]
    fn test_parse_let() {
        let expr: RecExpr<ArkLang> =
            "(let x 42 (add Int Int x x))".parse().unwrap();
        assert!(expr.as_ref().len() >= 4);
    }

    #[test]
    fn test_parse_poly() {
        let expr: RecExpr<ArkLang> =
            "(eval DensePoly (coerce (arrayof Field) DensePoly (array 1 2 3)) 5)".parse().unwrap();
        assert!(expr.as_ref().len() >= 8);
    }

    #[test]
    fn test_roundtrip_display_parse() {
        let expr: RecExpr<ArkLang> = "(add Int Int (mul Int Int 3 x) (neg Int y))".parse().unwrap();
        let s = expr.to_string();
        let expr2: RecExpr<ArkLang> = s.parse().unwrap();
        assert_eq!(expr, expr2);
    }
}
