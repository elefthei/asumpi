// arkΣΠ Runtime Value Types

use ark_bls12_381::{Fr, G1Projective};
use ark_ec::CurveGroup;
use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial as SparseUVPolynomial},
    polynomial::multivariate::{SparsePolynomial as MVSparsePolynomial, SparseTerm},
    DenseMultilinearExtension, SparseMultilinearExtension,
    DenseUVPolynomial, DenseMVPolynomial,
    MultilinearExtension, Polynomial as PolyTrait,
};
use std::fmt;

/// Runtime value produced by evaluating an arkΣΠ expression.
#[derive(Clone, Debug)]
pub enum Value {
    /// Finite field element (BLS12-381 scalar field Fr)
    Field(Fr),
    /// Elliptic curve point (BLS12-381 G1)
    Curve(G1Projective),
    /// Homogeneous array of values (all elements same type)
    Array(Vec<Value>),
    /// Univariate polynomial over Fr
    Polynomial(DensePolynomial<Fr>),
    /// Multilinear extension over Fr (evaluations on boolean hypercube)
    MLE(DenseMultilinearExtension<Fr>),
    /// Sparse multivariate polynomial over Fr
    MVPoly(MVSparsePolynomial<Fr, SparseTerm>),
    /// Sparse univariate polynomial over Fr
    SparseUVPoly(SparseUVPolynomial<Fr>),
    /// Sparse multilinear extension over Fr
    SparseMLE(SparseMultilinearExtension<Fr>),
    /// Pair of values (used for pdiv quotient+remainder, etc.)
    Pair(Box<Value>, Box<Value>),
    /// Boolean value
    Bool(bool),
    /// Integer value (for indices, exponents, etc.)
    Int(i64),
}

impl Value {
    /// Extract as field element, coercing Int → Fr automatically.
    pub fn as_field(&self) -> Result<Fr, EvalError> {
        match self {
            Value::Field(f) => Ok(*f),
            Value::Int(n) => Ok(int_to_fr(*n)),
            _ => Err(EvalError::TypeError(format!(
                "expected field element, got {}",
                self.type_name()
            ))),
        }
    }

    /// Extract as curve point.
    pub fn as_curve(&self) -> Result<G1Projective, EvalError> {
        match self {
            Value::Curve(p) => Ok(*p),
            _ => Err(EvalError::TypeError(format!(
                "expected curve point, got {}",
                self.type_name()
            ))),
        }
    }

    /// Extract as array.
    pub fn as_array(&self) -> Result<Vec<Value>, EvalError> {
        match self {
            Value::Array(v) => Ok(v.clone()),
            _ => Err(EvalError::TypeError(format!(
                "expected array, got {}",
                self.type_name()
            ))),
        }
    }

    /// Extract as polynomial.
    pub fn as_polynomial(&self) -> Result<DensePolynomial<Fr>, EvalError> {
        match self {
            Value::Polynomial(p) => Ok(p.clone()),
            _ => Err(EvalError::TypeError(format!(
                "expected polynomial, got {}",
                self.type_name()
            ))),
        }
    }

    /// Extract as multilinear extension.
    pub fn as_mle(&self) -> Result<DenseMultilinearExtension<Fr>, EvalError> {
        match self {
            Value::MLE(m) => Ok(m.clone()),
            _ => Err(EvalError::TypeError(format!(
                "expected MLE, got {}",
                self.type_name()
            ))),
        }
    }

    /// Extract as multivariate polynomial.
    pub fn as_mvpoly(&self) -> Result<MVSparsePolynomial<Fr, SparseTerm>, EvalError> {
        match self {
            Value::MVPoly(p) => Ok(p.clone()),
            _ => Err(EvalError::TypeError(format!(
                "expected multivariate polynomial, got {}",
                self.type_name()
            ))),
        }
    }

    /// Extract as sparse univariate polynomial.
    pub fn as_sparse_uv_poly(&self) -> Result<SparseUVPolynomial<Fr>, EvalError> {
        match self {
            Value::SparseUVPoly(p) => Ok(p.clone()),
            _ => Err(EvalError::TypeError(format!(
                "expected sparse univariate polynomial, got {}",
                self.type_name()
            ))),
        }
    }

    /// Extract as sparse multilinear extension.
    pub fn as_sparse_mle(&self) -> Result<SparseMultilinearExtension<Fr>, EvalError> {
        match self {
            Value::SparseMLE(m) => Ok(m.clone()),
            _ => Err(EvalError::TypeError(format!(
                "expected sparse MLE, got {}",
                self.type_name()
            ))),
        }
    }

    /// Extract as boolean.
    pub fn as_bool(&self) -> Result<bool, EvalError> {
        match self {
            Value::Bool(b) => Ok(*b),
            _ => Err(EvalError::TypeError(format!(
                "expected boolean, got {}",
                self.type_name()
            ))),
        }
    }

    /// Extract as integer.
    pub fn as_int(&self) -> Result<i64, EvalError> {
        match self {
            Value::Int(n) => Ok(*n),
            _ => Err(EvalError::TypeError(format!(
                "expected integer, got {}",
                self.type_name()
            ))),
        }
    }

    /// Extract as pair.
    pub fn as_pair(&self) -> Result<(&Value, &Value), EvalError> {
        match self {
            Value::Pair(a, b) => Ok((a, b)),
            _ => Err(EvalError::TypeError(format!(
                "expected pair, got {}",
                self.type_name()
            ))),
        }
    }

    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Field(_) => "Field",
            Value::Curve(_) => "Curve",
            Value::Array(_) => "Array",
            Value::Polynomial(_) => "Polynomial",
            Value::MLE(_) => "MLE",
            Value::MVPoly(_) => "MVPoly",
            Value::SparseUVPoly(_) => "SparseUVPoly",
            Value::SparseMLE(_) => "SparseMLE",
            Value::Pair(_, _) => "Pair",
            Value::Bool(_) => "Bool",
            Value::Int(_) => "Int",
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Field(fr) => write!(f, "Field({})", fr),
            Value::Curve(p) => {
                let aff = p.into_affine();
                write!(f, "Curve({})", aff)
            }
            Value::Array(v) => {
                write!(f, "Array[")?;
                for (i, val) in v.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", val)?;
                }
                write!(f, "]")
            }
            Value::Polynomial(p) => write!(f, "Poly(deg={})", p.coeffs().len().saturating_sub(1)),
            Value::MLE(m) => write!(f, "MLE(nvars={})", m.num_vars()),
            Value::MVPoly(p) => write!(f, "MVPoly(nvars={}, deg={})", p.num_vars(), p.degree()),
            Value::SparseUVPoly(p) => write!(f, "SparseUVPoly(deg={})", p.degree()),
            Value::SparseMLE(m) => write!(f, "SparseMLE(nvars={})", m.num_vars()),
            Value::Pair(a, b) => write!(f, "Pair({}, {})", a, b),
            Value::Bool(b) => write!(f, "Bool({})", b),
            Value::Int(n) => write!(f, "Int({})", n),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Field(a), Value::Field(b)) => a == b,
            (Value::Curve(a), Value::Curve(b)) => a.into_affine() == b.into_affine(),
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Array(a), Value::Array(b)) => a == b,
            (Value::Polynomial(a), Value::Polynomial(b)) => a.coeffs == b.coeffs,
            (Value::MLE(a), Value::MLE(b)) => a == b,
            (Value::MVPoly(a), Value::MVPoly(b)) => a == b,
            (Value::SparseUVPoly(a), Value::SparseUVPoly(b)) => a == b,
            (Value::SparseMLE(a), Value::SparseMLE(b)) => a == b,
            (Value::Pair(a1, a2), Value::Pair(b1, b2)) => a1 == b1 && a2 == b2,
            // Cross-type: Int and Field can be compared
            (Value::Int(n), Value::Field(f)) | (Value::Field(f), Value::Int(n)) => {
                int_to_fr(*n) == *f
            }
            _ => false,
        }
    }
}

/// Evaluation error.
#[derive(Clone, Debug)]
pub enum EvalError {
    UnboundVariable(String),
    TypeError(String),
    TypeMismatch { expected: String, got: String },
    DivisionByZero,
    IndexOutOfBounds { index: usize, len: usize },
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::UnboundVariable(name) => write!(f, "unbound variable: {}", name),
            EvalError::TypeError(msg) => write!(f, "type error: {}", msg),
            EvalError::TypeMismatch { expected, got } => {
                write!(f, "type mismatch: expected {}, got {}", expected, got)
            }
            EvalError::DivisionByZero => write!(f, "division by zero"),
            EvalError::IndexOutOfBounds { index, len } => {
                write!(f, "index {} out of bounds (len {})", index, len)
            }
        }
    }
}

impl std::error::Error for EvalError {}

/// Convert a signed integer to a field element.
pub fn int_to_fr(n: i64) -> Fr {
    if n >= 0 {
        Fr::from(n as u64)
    } else {
        -Fr::from((-n) as u64)
    }
}

/// Check that all values in a slice have the same type.
/// Returns Ok(()) if empty or homogeneous, Err otherwise.
pub fn check_homogeneous(vals: &[Value]) -> Result<(), EvalError> {
    if vals.len() <= 1 {
        return Ok(());
    }
    let expected = vals[0].type_name();
    for (i, v) in vals.iter().enumerate().skip(1) {
        let got = v.type_name();
        if got != expected {
            return Err(EvalError::TypeMismatch {
                expected: format!("{} (element 0)", expected),
                got: format!("{} (element {})", got, i),
            });
        }
    }
    Ok(())
}
