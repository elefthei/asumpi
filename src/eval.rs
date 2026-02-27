// arkΣΠ Runtime Evaluator
//
// Recursively evaluates a RecExpr<ArkLang> against arkworks types.
// Uses type dispatch for generic operations (add, mul, neg, etc).

use std::collections::HashMap;

use ark_bls12_381::Fr;
use ark_ff::{Field, One, Zero};
use ark_poly::{
    univariate::{DensePolynomial, DenseOrSparsePolynomial, SparsePolynomial as SparseUVPolynomial},
    polynomial::multivariate::{SparsePolynomial as MVSparsePolynomial, SparseTerm, Term},
    DenseMultilinearExtension, SparseMultilinearExtension,
    DenseUVPolynomial, DenseMVPolynomial,
    MultilinearExtension, Polynomial,
    EvaluationDomain, GeneralEvaluationDomain,
};
use egg::{Id, RecExpr, Symbol};

use crate::language::ArkLang;
use crate::value::{EvalError, Value, check_homogeneous, int_to_fr};

/// Environment mapping variable names to values.
pub type Env = HashMap<Symbol, Value>;

/// Evaluate an arkΣΠ expression with the given environment.
pub fn eval(expr: &RecExpr<ArkLang>, env: &Env) -> Result<Value, EvalError> {
    let root = Id::from(expr.as_ref().len() - 1);
    eval_id(expr, root, env)
}

/// Generic add for two Value operands.
fn value_add(va: Value, vb: Value) -> Result<Value, EvalError> {
    match (va, vb) {
        (Value::Field(a), Value::Field(b)) => Ok(Value::Field(a + b)),
        (Value::Int(a), Value::Int(b)) => {
            Ok(Value::Field(int_to_fr(a) + int_to_fr(b)))
        }
        (Value::Int(n), Value::Field(f)) | (Value::Field(f), Value::Int(n)) => {
            Ok(Value::Field(f + int_to_fr(n)))
        }
        (Value::Curve(a), Value::Curve(b)) => Ok(Value::Curve(a + b)),
        (Value::Polynomial(a), Value::Polynomial(b)) => Ok(Value::Polynomial(&a + &b)),
        (Value::SparseUVPoly(a), Value::SparseUVPoly(b)) => Ok(Value::SparseUVPoly(&a + &b)),
        (Value::MLE(a), Value::MLE(b)) => {
            if a.num_vars() != b.num_vars() {
                return Err(EvalError::TypeError(format!(
                    "add: MLE num_vars mismatch ({} vs {})", a.num_vars(), b.num_vars()
                )));
            }
            Ok(Value::MLE(&a + &b))
        }
        (Value::MVPoly(a), Value::MVPoly(b)) => Ok(Value::MVPoly(&a + &b)),
        (a, b) => Err(EvalError::TypeError(format!(
            "add: incompatible types {} and {}", a.type_name(), b.type_name()
        ))),
    }
}

/// Generic mul for two Value operands (ring types only).
fn value_mul(va: Value, vb: Value) -> Result<Value, EvalError> {
    match (va, vb) {
        (Value::Field(a), Value::Field(b)) => Ok(Value::Field(a * b)),
        (Value::Int(a), Value::Int(b)) => {
            Ok(Value::Field(int_to_fr(a) * int_to_fr(b)))
        }
        (Value::Int(n), Value::Field(f)) | (Value::Field(f), Value::Int(n)) => {
            Ok(Value::Field(f * int_to_fr(n)))
        }
        (Value::Polynomial(a), Value::Polynomial(b)) => Ok(Value::Polynomial(&a * &b)),
        (a, b) => Err(EvalError::TypeError(format!(
            "mul: incompatible types {} and {}", a.type_name(), b.type_name()
        ))),
    }
}

/// Evaluate a specific node in the expression tree.
fn eval_id(expr: &RecExpr<ArkLang>, id: Id, env: &Env) -> Result<Value, EvalError> {
    let node = &expr[id];
    match node {
        // ── Constants ──
        ArkLang::Num(n) => Ok(Value::Int(*n)),

        // ── Variables ──
        ArkLang::Symbol(s) => env
            .get(s)
            .cloned()
            .ok_or_else(|| EvalError::UnboundVariable(s.to_string())),

        // ── Generic Add ──
        ArkLang::Add([a, b]) => {
            let va = eval_id(expr, *a, env)?;
            let vb = eval_id(expr, *b, env)?;
            value_add(va, vb)
        }

        // ── Generic Neg ──
        ArkLang::Neg([a]) => {
            let va = eval_id(expr, *a, env)?;
            match va {
                Value::Field(f) => Ok(Value::Field(-f)),
                Value::Int(n) => Ok(Value::Field(-int_to_fr(n))),
                Value::Curve(p) => Ok(Value::Curve(-p)),
                Value::Polynomial(p) => Ok(Value::Polynomial(-p)),
                Value::SparseUVPoly(p) => {
                    // Negate by negating all coefficients
                    let neg_coeffs: Vec<(usize, Fr)> = p.to_vec().iter()
                        .map(|(i, c)| (*i, -(*c)))
                        .collect();
                    Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(neg_coeffs)))
                }
                Value::MLE(m) => {
                    let nv = m.num_vars();
                    let neg_evals: Vec<Fr> = m.to_evaluations().iter().map(|v| -(*v)).collect();
                    Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(nv, neg_evals)))
                }
                Value::MVPoly(p) => {
                    // Negate: multiply all coefficients by -1
                    let nv = p.num_vars();
                    let neg_terms: Vec<(Fr, SparseTerm)> = p.terms().iter()
                        .map(|(c, t)| (-(*c), t.clone()))
                        .collect();
                    Ok(Value::MVPoly(MVSparsePolynomial::from_coefficients_vec(nv, neg_terms)))
                }
                v => Err(EvalError::TypeError(format!(
                    "neg: unsupported type {}", v.type_name()
                ))),
            }
        }

        // ── Generic Mul ──
        ArkLang::Mul([a, b]) => {
            let va = eval_id(expr, *a, env)?;
            let vb = eval_id(expr, *b, env)?;
            value_mul(va, vb)
        }

        // ── Inv (field only) ──
        ArkLang::Inv([a]) => {
            let va = eval_id(expr, *a, env)?.as_field()?;
            va.inverse()
                .map(Value::Field)
                .ok_or(EvalError::DivisionByZero)
        }

        // ── Scale: scalar * value ──
        ArkLang::Scale([c, a]) => {
            let vc = eval_id(expr, *c, env)?.as_field()?;
            let va = eval_id(expr, *a, env)?;
            match va {
                Value::Field(f) => Ok(Value::Field(vc * f)),
                Value::Int(n) => Ok(Value::Field(vc * int_to_fr(n))),
                Value::Curve(p) => Ok(Value::Curve(p * vc)),
                Value::Polynomial(p) => Ok(Value::Polynomial(&p * vc)),
                Value::SparseUVPoly(p) => {
                    let scaled: Vec<(usize, Fr)> = p.to_vec().iter()
                        .map(|(i, coeff)| (*i, *coeff * vc))
                        .collect();
                    Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(scaled)))
                }
                Value::MLE(m) => {
                    let nv = m.num_vars();
                    let scaled_evals: Vec<Fr> = m.to_evaluations().iter().map(|v| *v * vc).collect();
                    Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(nv, scaled_evals)))
                }
                Value::MVPoly(p) => {
                    let nv = p.num_vars();
                    let scaled_terms: Vec<(Fr, SparseTerm)> = p.terms().iter()
                        .map(|(c, t)| (*c * vc, t.clone()))
                        .collect();
                    Ok(Value::MVPoly(MVSparsePolynomial::from_coefficients_vec(nv, scaled_terms)))
                }
                v => Err(EvalError::TypeError(format!(
                    "scale: unsupported target type {}", v.type_name()
                ))),
            }
        }

        // ── Pow (field only) ──
        ArkLang::Pow([base, exp]) => {
            let vb = eval_id(expr, *base, env)?.as_field()?;
            let ve = eval_id(expr, *exp, env)?.as_int()?;
            if ve >= 0 {
                let mut result = Fr::from(1u64);
                for _ in 0..ve {
                    result *= vb;
                }
                Ok(Value::Field(result))
            } else {
                let inv = vb.inverse().ok_or(EvalError::DivisionByZero)?;
                let mut result = Fr::from(1u64);
                for _ in 0..(-ve) {
                    result *= inv;
                }
                Ok(Value::Field(result))
            }
        }

        // ── Eval: evaluate polynomial/MLE at a point ──
        ArkLang::Eval([f, x]) => {
            let vf = eval_id(expr, *f, env)?;
            match vf {
                Value::Polynomial(p) => {
                    let xv = eval_id(expr, *x, env)?.as_field()?;
                    Ok(Value::Field(p.evaluate(&xv)))
                }
                Value::SparseUVPoly(p) => {
                    let xv = eval_id(expr, *x, env)?.as_field()?;
                    Ok(Value::Field(Polynomial::evaluate(&p, &xv)))
                }
                Value::MLE(m) => {
                    let arr = eval_id(expr, *x, env)?.as_array()?;
                    let point_fr: Vec<Fr> = arr.into_iter()
                        .map(|v| v.as_field())
                        .collect::<Result<_, _>>()?;
                    Ok(Value::Field(m.evaluate(&point_fr)))
                }
                Value::SparseMLE(m) => {
                    let arr = eval_id(expr, *x, env)?.as_array()?;
                    let point_fr: Vec<Fr> = arr.into_iter()
                        .map(|v| v.as_field())
                        .collect::<Result<_, _>>()?;
                    Ok(Value::Field(m.evaluate(&point_fr)))
                }
                Value::MVPoly(p) => {
                    let arr = eval_id(expr, *x, env)?.as_array()?;
                    let point_fr: Vec<Fr> = arr.into_iter()
                        .map(|v| v.as_field())
                        .collect::<Result<_, _>>()?;
                    Ok(Value::Field(p.evaluate(&point_fr)))
                }
                v => Err(EvalError::TypeError(format!(
                    "eval: expected polynomial/MLE type, got {}", v.type_name()
                ))),
            }
        }

        // ── Deg ──
        ArkLang::Deg([p]) => {
            let vp = eval_id(expr, *p, env)?;
            match vp {
                Value::Polynomial(p) => Ok(Value::Int(p.degree() as i64)),
                Value::SparseUVPoly(p) => Ok(Value::Int(p.degree() as i64)),
                Value::MVPoly(p) => Ok(Value::Int(p.degree() as i64)),
                Value::MLE(m) => Ok(Value::Int(m.num_vars() as i64)),
                Value::SparseMLE(m) => Ok(Value::Int(m.num_vars() as i64)),
                v => Err(EvalError::TypeError(format!(
                    "deg: unsupported type {}", v.type_name()
                ))),
            }
        }

        // ── NVars ──
        ArkLang::NVars([p]) => {
            let vp = eval_id(expr, *p, env)?;
            match vp {
                Value::MLE(m) => Ok(Value::Int(m.num_vars() as i64)),
                Value::SparseMLE(m) => Ok(Value::Int(m.num_vars() as i64)),
                Value::MVPoly(p) => Ok(Value::Int(p.num_vars() as i64)),
                Value::Polynomial(_) | Value::SparseUVPoly(_) => Ok(Value::Int(1)),
                v => Err(EvalError::TypeError(format!(
                    "nvars: unsupported type {}", v.type_name()
                ))),
            }
        }

        // ── Polynomial Constructors ──
        ArkLang::PolyDUV(_) | ArkLang::PolySUV(_) | ArkLang::PolyDMLE(_)
        | ArkLang::PolySMLE(_) | ArkLang::PolyMV(_) => {
            eval_poly_constructor(expr, node, env)
        }

        // ── Symbolic Polynomial Constructor ──
        ArkLang::Poly(children) => {
            eval_symbolic_poly(expr, children, env)
        }
        ArkLang::Ids(_) => {
            Err(EvalError::TypeError("ids: cannot be evaluated standalone, use inside (poly ...)".into()))
        }

        // ── Poly-Specific: PDiv, Fix ──
        ArkLang::PDiv(_) | ArkLang::Fix(_) => {
            eval_poly_specific(expr, node, env)
        }

        // ── Tuples ──
        ArkLang::Pair([a, b]) => {
            let va = eval_id(expr, *a, env)?;
            let vb = eval_id(expr, *b, env)?;
            Ok(Value::Pair(Box::new(va), Box::new(vb)))
        }
        ArkLang::Fst([p]) => {
            let vp = eval_id(expr, *p, env)?;
            let (a, _) = vp.as_pair()?;
            Ok(a.clone())
        }
        ArkLang::Snd([p]) => {
            let vp = eval_id(expr, *p, env)?;
            let (_, b) = vp.as_pair()?;
            Ok(b.clone())
        }

        // ── FFT / Domain ──
        ArkLang::Domain([n]) => {
            let size = eval_id(expr, *n, env)?.as_int()? as usize;
            let domain = GeneralEvaluationDomain::<Fr>::new(size)
                .ok_or_else(|| EvalError::TypeError(format!(
                    "domain: cannot create evaluation domain of size {}", size
                )))?;
            let elements: Vec<Value> = domain.elements().map(Value::Field).collect();
            Ok(Value::Array(elements))
        }

        ArkLang::Fft([n, p]) => {
            let size = eval_id(expr, *n, env)?.as_int()? as usize;
            let domain = GeneralEvaluationDomain::<Fr>::new(size)
                .ok_or_else(|| EvalError::TypeError(format!(
                    "fft: cannot create evaluation domain of size {}", size
                )))?;
            let vp = eval_id(expr, *p, env)?;
            let coeffs: Vec<Fr> = match vp {
                Value::Polynomial(poly) => poly.coeffs.clone(),
                Value::SparseUVPoly(sp) => {
                    let deg = sp.degree();
                    let mut dense = vec![Fr::zero(); deg + 1];
                    for (i, c) in sp.to_vec().iter() {
                        if *i <= deg { dense[*i] = *c; }
                    }
                    dense
                }
                Value::Array(arr) => arr.into_iter()
                    .map(|v| v.as_field())
                    .collect::<Result<_, _>>()?,
                v => return Err(EvalError::TypeError(format!(
                    "fft: expected polynomial or array, got {}", v.type_name()
                ))),
            };
            let evals = domain.fft(&coeffs);
            Ok(Value::Array(evals.into_iter().map(Value::Field).collect()))
        }

        ArkLang::Ifft([n, e]) => {
            let size = eval_id(expr, *n, env)?.as_int()? as usize;
            let domain = GeneralEvaluationDomain::<Fr>::new(size)
                .ok_or_else(|| EvalError::TypeError(format!(
                    "ifft: cannot create evaluation domain of size {}", size
                )))?;
            let ve = eval_id(expr, *e, env)?.as_array()?;
            let evals: Vec<Fr> = ve.into_iter()
                .map(|v| v.as_field())
                .collect::<Result<_, _>>()?;
            let coeffs = domain.ifft(&evals);
            // Trim trailing zeros
            let mut trimmed = coeffs;
            while trimmed.len() > 1 && trimmed.last().map_or(false, |c| c.is_zero()) {
                trimmed.pop();
            }
            Ok(Value::Polynomial(DensePolynomial::from_coefficients_vec(trimmed)))
        }

        // ── Indexed Sum/Product ──
        ArkLang::Bound([_lo, _hi]) => {
            Err(EvalError::TypeError(
                "cannot evaluate symbolic bound; specialize sizes first".into()
            ))
        }

        ArkLang::Sigma([idx, start, end, body]) => {
            let idx_sym = match &expr[*idx] {
                ArkLang::Symbol(s) => *s,
                _ => return Err(EvalError::TypeError(
                    "Σ: first argument must be a variable name".into(),
                )),
            };
            let start_val = eval_id(expr, *start, env)?.as_int()?;
            let end_val = eval_id(expr, *end, env)?.as_int()?;
            if start_val >= end_val {
                return Ok(Value::Int(0));
            }
            let mut acc: Option<Value> = None;
            for i in start_val..end_val {
                let mut new_env = env.clone();
                new_env.insert(idx_sym, Value::Int(i));
                let val = eval_id(expr, *body, &new_env)?;
                acc = Some(match acc {
                    None => val,
                    Some(prev) => value_add(prev, val)?,
                });
            }
            Ok(acc.unwrap_or(Value::Int(0)))
        }

        ArkLang::Pi([idx, start, end, body]) => {
            let idx_sym = match &expr[*idx] {
                ArkLang::Symbol(s) => *s,
                _ => return Err(EvalError::TypeError(
                    "Π: first argument must be a variable name".into(),
                )),
            };
            let start_val = eval_id(expr, *start, env)?.as_int()?;
            let end_val = eval_id(expr, *end, env)?.as_int()?;
            if start_val >= end_val {
                return Ok(Value::Int(1));
            }
            let mut acc: Option<Value> = None;
            for i in start_val..end_val {
                let mut new_env = env.clone();
                new_env.insert(idx_sym, Value::Int(i));
                let val = eval_id(expr, *body, &new_env)?;
                acc = Some(match acc {
                    None => val,
                    Some(prev) => value_mul(prev, val)?,
                });
            }
            Ok(acc.unwrap_or(Value::Int(1)))
        }

        // ── Conversions ──
        ArkLang::Densify(_) | ArkLang::Sparsify(_) | ArkLang::AsUV(_) | ArkLang::AsMLE(_) => {
            eval_conversion(expr, node, env)
        }

        // ── Array Operations ──
        ArkLang::MkArray(children) => {
            let vals: Vec<Value> = children
                .iter()
                .map(|id| eval_id(expr, *id, env))
                .collect::<Result<_, _>>()?;
            check_homogeneous(&vals)?;
            Ok(Value::Array(vals))
        }

        ArkLang::Select([arr, idx]) => {
            let va = eval_id(expr, *arr, env)?.as_array()?;
            let vi = eval_id(expr, *idx, env)?.as_int()?;
            let idx = vi as usize;
            if idx >= va.len() {
                return Err(EvalError::IndexOutOfBounds {
                    index: idx,
                    len: va.len(),
                });
            }
            Ok(va[idx].clone())
        }

        ArkLang::Store([arr, idx, val]) => {
            let mut va = eval_id(expr, *arr, env)?.as_array()?;
            let vi = eval_id(expr, *idx, env)?.as_int()?;
            let vv = eval_id(expr, *val, env)?;
            let idx = vi as usize;
            if idx >= va.len() {
                return Err(EvalError::IndexOutOfBounds {
                    index: idx,
                    len: va.len(),
                });
            }
            if !va.is_empty() {
                let expected = va[0].type_name();
                let got = vv.type_name();
                if got != expected {
                    return Err(EvalError::TypeMismatch {
                        expected: expected.to_string(),
                        got: got.to_string(),
                    });
                }
            }
            va[idx] = vv;
            Ok(Value::Array(va))
        }

        ArkLang::ALen([arr]) => {
            let va = eval_id(expr, *arr, env)?.as_array()?;
            Ok(Value::Int(va.len() as i64))
        }

        ArkLang::AAdd([a, b]) => {
            let va = eval_id(expr, *a, env)?.as_array()?;
            let vb = eval_id(expr, *b, env)?.as_array()?;
            let len = va.len().max(vb.len());
            let mut result = Vec::with_capacity(len);
            for i in 0..len {
                let fa = if i < va.len() { va[i].as_field()? } else { Fr::zero() };
                let fb = if i < vb.len() { vb[i].as_field()? } else { Fr::zero() };
                result.push(Value::Field(fa + fb));
            }
            Ok(Value::Array(result))
        }

        // ── Let Binding ──
        ArkLang::Let([name, val, body]) => {
            let name_sym = match &expr[*name] {
                ArkLang::Symbol(s) => *s,
                _ => {
                    return Err(EvalError::TypeError(
                        "let: first argument must be a variable name".into(),
                    ))
                }
            };
            let val = eval_id(expr, *val, env)?;
            let mut new_env = env.clone();
            new_env.insert(name_sym, val);
            eval_id(expr, *body, &new_env)
        }

        // ── Conditional ──
        ArkLang::If([cond, then_, else_]) => {
            let vc = eval_id(expr, *cond, env)?.as_bool()?;
            if vc {
                eval_id(expr, *then_, env)
            } else {
                eval_id(expr, *else_, env)
            }
        }

        // ── Comparison ──
        ArkLang::Eq([a, b]) => {
            let va = eval_id(expr, *a, env)?.as_field()?;
            let vb = eval_id(expr, *b, env)?.as_field()?;
            Ok(Value::Bool(va == vb))
        }
    }
}

/// Evaluate polynomial constructor nodes.
fn eval_poly_constructor(expr: &RecExpr<ArkLang>, node: &ArkLang, env: &Env) -> Result<Value, EvalError> {
    match node {
        ArkLang::PolyDUV(children) => {
            let coeffs: Vec<Fr> = children
                .iter()
                .map(|id| eval_id(expr, *id, env)?.as_field())
                .collect::<Result<_, _>>()?;
            Ok(Value::Polynomial(DensePolynomial::from_coefficients_vec(coeffs)))
        }

        ArkLang::PolySUV(children) => {
            if children.len() % 2 != 0 {
                return Err(EvalError::TypeError(
                    "poly:suv: expected even number of arguments (power coeff pairs)".into(),
                ));
            }
            let mut terms = Vec::new();
            for chunk in children.chunks(2) {
                let pow = eval_id(expr, chunk[0], env)?.as_int()? as usize;
                let coeff = eval_id(expr, chunk[1], env)?.as_field()?;
                terms.push((pow, coeff));
            }
            Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(terms)))
        }

        ArkLang::PolyDMLE([nvars, evals]) => {
            let n = eval_id(expr, *nvars, env)?.as_int()?;
            let vals = eval_id(expr, *evals, env)?.as_array()?;
            let expected_len = 1usize << (n as usize);
            if vals.len() != expected_len {
                return Err(EvalError::TypeError(format!(
                    "poly:dmle: expected {} evaluations for {} variables, got {}",
                    expected_len, n, vals.len()
                )));
            }
            let fr_vals: Vec<Fr> = vals.into_iter()
                .map(|v| v.as_field())
                .collect::<Result<_, _>>()?;
            Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(n as usize, fr_vals)))
        }

        ArkLang::PolySMLE([nvars, evals]) => {
            let nv = eval_id(expr, *nvars, env)?.as_int()? as usize;
            let arr = eval_id(expr, *evals, env)?.as_array()?;
            if arr.len() % 2 != 0 {
                return Err(EvalError::TypeError(
                    "poly:smle: evals_array must have even length (index value pairs)".into(),
                ));
            }
            let mut evals_vec = Vec::new();
            for chunk in arr.chunks(2) {
                let idx = chunk[0].as_int()? as usize;
                let val = chunk[1].as_field()?;
                evals_vec.push((idx, val));
            }
            Ok(Value::SparseMLE(SparseMultilinearExtension::from_evaluations(nv, &evals_vec)))
        }

        ArkLang::PolyMV([nvars, coeffs, terms]) => {
            let n = eval_id(expr, *nvars, env)?.as_int()? as usize;
            let coeffs_arr = eval_id(expr, *coeffs, env)?.as_array()?;
            let terms_arr = eval_id(expr, *terms, env)?.as_array()?;
            if coeffs_arr.len() != terms_arr.len() {
                return Err(EvalError::TypeError(format!(
                    "poly:mv: coefficients ({}) and terms ({}) must have same length",
                    coeffs_arr.len(), terms_arr.len()
                )));
            }
            let mut term_pairs: Vec<(Fr, SparseTerm)> = Vec::new();
            for (c_val, t_val) in coeffs_arr.into_iter().zip(terms_arr.into_iter()) {
                let coeff = c_val.as_field()?;
                let t_arr = t_val.as_array()?;
                if t_arr.len() % 2 != 0 {
                    return Err(EvalError::TypeError(
                        "poly:mv: each term must have even-length array [var, power, ...]".into()
                    ));
                }
                let mut pairs = Vec::new();
                for chunk in t_arr.chunks(2) {
                    let var = chunk[0].as_int()? as usize;
                    let pow = chunk[1].as_int()? as usize;
                    pairs.push((var, pow));
                }
                term_pairs.push((coeff, SparseTerm::new(pairs)));
            }
            Ok(Value::MVPoly(MVSparsePolynomial::from_coefficients_vec(n, term_pairs)))
        }

        _ => unreachable!("eval_poly_constructor called with non-constructor node"),
    }
}

/// Evaluate poly-specific operations (division, fix).
fn eval_poly_specific(expr: &RecExpr<ArkLang>, node: &ArkLang, env: &Env) -> Result<Value, EvalError> {
    match node {
        ArkLang::PDiv([a, b]) => {
            let va = eval_id(expr, *a, env)?.as_polynomial()?;
            let vb = eval_id(expr, *b, env)?.as_polynomial()?;
            if vb.is_zero() {
                return Err(EvalError::DivisionByZero);
            }
            let a_sparse = DenseOrSparsePolynomial::from(&va);
            let b_sparse = DenseOrSparsePolynomial::from(&vb);
            let (q, r) = a_sparse.divide_with_q_and_r(&b_sparse)
                .ok_or(EvalError::DivisionByZero)?;
            Ok(Value::Pair(Box::new(Value::Polynomial(q)), Box::new(Value::Polynomial(r))))
        }

        ArkLang::Fix([mle, partial]) => {
            let vm = eval_id(expr, *mle, env)?.as_mle()?;
            let vp = eval_id(expr, *partial, env)?.as_array()?;
            let partial_fr: Vec<Fr> = vp.into_iter()
                .map(|v| v.as_field())
                .collect::<Result<_, _>>()?;
            Ok(Value::MLE(vm.fix_variables(&partial_fr)))
        }

        _ => unreachable!("eval_poly_specific called with non-poly-specific node"),
    }
}

/// Evaluate conversion nodes (densify, sparsify, as-uv, as-mle).
fn eval_conversion(expr: &RecExpr<ArkLang>, node: &ArkLang, env: &Env) -> Result<Value, EvalError> {
    match node {
        ArkLang::Densify([x]) => {
            let vx = eval_id(expr, *x, env)?;
            match vx {
                Value::SparseUVPoly(p) => {
                    let deg = p.degree();
                    let mut coeffs = vec![Fr::zero(); deg + 1];
                    for (i, c) in p.to_vec().iter() {
                        if *i <= deg {
                            coeffs[*i] = *c;
                        }
                    }
                    Ok(Value::Polynomial(DensePolynomial::from_coefficients_vec(coeffs)))
                }
                Value::SparseMLE(m) => {
                    let nv = m.num_vars();
                    let evals = m.to_evaluations();
                    Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(nv, evals)))
                }
                v => Err(EvalError::TypeError(format!(
                    "densify: expected sparse type, got {}", v.type_name()
                ))),
            }
        }

        ArkLang::Sparsify([x]) => {
            let vx = eval_id(expr, *x, env)?;
            match vx {
                Value::Polynomial(p) => {
                    let sparse_coeffs: Vec<(usize, Fr)> = p.coeffs.iter()
                        .enumerate()
                        .filter(|(_, c)| !c.is_zero())
                        .map(|(i, c)| (i, *c))
                        .collect();
                    Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(sparse_coeffs)))
                }
                Value::MLE(m) => {
                    let nv = m.num_vars();
                    let sparse_evals: Vec<(usize, Fr)> = m.to_evaluations().iter()
                        .enumerate()
                        .filter(|(_, v)| !v.is_zero())
                        .map(|(i, v)| (i, *v))
                        .collect();
                    Ok(Value::SparseMLE(SparseMultilinearExtension::from_evaluations(nv, &sparse_evals)))
                }
                v => Err(EvalError::TypeError(format!(
                    "sparsify: expected dense type, got {}", v.type_name()
                ))),
            }
        }

        ArkLang::AsUV([x]) => {
            let vx = eval_id(expr, *x, env)?;
            match vx {
                Value::MLE(m) => {
                    if m.num_vars() != 1 {
                        return Err(EvalError::TypeError(format!(
                            "as-uv: MLE must have 1 variable, got {}", m.num_vars()
                        )));
                    }
                    let evals = m.to_evaluations();
                    let c0 = evals[0];
                    let c1 = evals[1] - evals[0];
                    Ok(Value::Polynomial(DensePolynomial::from_coefficients_vec(vec![c0, c1])))
                }
                Value::SparseMLE(m) => {
                    if m.num_vars() != 1 {
                        return Err(EvalError::TypeError(format!(
                            "as-uv: SparseMLE must have 1 variable, got {}", m.num_vars()
                        )));
                    }
                    let evals = m.to_evaluations();
                    let c0 = evals[0];
                    let c1 = evals[1] - evals[0];
                    let mut terms = Vec::new();
                    if !c0.is_zero() { terms.push((0, c0)); }
                    if !c1.is_zero() { terms.push((1, c1)); }
                    Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(terms)))
                }
                v => Err(EvalError::TypeError(format!(
                    "as-uv: expected MLE type, got {}", v.type_name()
                ))),
            }
        }

        ArkLang::AsMLE([x]) => {
            let vx = eval_id(expr, *x, env)?;
            match vx {
                Value::Polynomial(p) => {
                    let v0 = p.evaluate(&Fr::from(0u64));
                    let v1 = p.evaluate(&Fr::from(1u64));
                    Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(1, vec![v0, v1])))
                }
                Value::SparseUVPoly(p) => {
                    let v0 = Polynomial::evaluate(&p, &Fr::from(0u64));
                    let v1 = Polynomial::evaluate(&p, &Fr::from(1u64));
                    let mut evals = Vec::new();
                    if !v0.is_zero() { evals.push((0, v0)); }
                    if !v1.is_zero() { evals.push((1, v1)); }
                    Ok(Value::SparseMLE(SparseMultilinearExtension::from_evaluations(1, &evals)))
                }
                v => Err(EvalError::TypeError(format!(
                    "as-mle: expected UV polynomial type, got {}", v.type_name()
                ))),
            }
        }

        _ => unreachable!("eval_conversion called with non-conversion node"),
    }
}

/// Evaluate a symbolic polynomial constructor `(poly (ids x y ...) term1 term2 ...)`.
fn eval_symbolic_poly(
    expr: &RecExpr<ArkLang>,
    children: &Box<[Id]>,
    env: &Env,
) -> Result<Value, EvalError> {
    if children.len() < 2 {
        return Err(EvalError::TypeError("poly: need (ids ...) and at least one term".into()));
    }
    // Extract variable names from the ids node
    let ids_node = &expr[children[0]];
    let var_names: Vec<Symbol> = match ids_node {
        ArkLang::Ids(ids) => {
            ids.iter().map(|id| {
                match &expr[*id] {
                    ArkLang::Symbol(s) => Ok(*s),
                    _ => Err(EvalError::TypeError("ids: all children must be symbols".into())),
                }
            }).collect::<Result<Vec<_>, _>>()?
        }
        _ => return Err(EvalError::TypeError("poly: first argument must be (ids ...)".into())),
    };
    let num_vars = var_names.len();
    if num_vars == 0 {
        return Err(EvalError::TypeError("poly: ids must declare at least one variable".into()));
    }

    // Interpret each term as a monomial
    let mut monomials: Vec<(Fr, Vec<usize>)> = Vec::new();
    for i in 1..children.len() {
        let (coeff, exps) = interpret_monomial(expr, children[i], &var_names, num_vars, env)?;
        if !coeff.is_zero() {
            monomials.push((coeff, exps));
        }
    }

    if num_vars == 1 {
        // Build SparseUVPoly: Vec<(usize, Fr)> = [(power, coeff), ...]
        let terms: Vec<(usize, Fr)> = monomials.into_iter()
            .map(|(c, exps)| (exps[0], c))
            .collect();
        Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(terms)))
    } else {
        // Build MVPoly: Vec<(Fr, SparseTerm)>
        let terms: Vec<(Fr, SparseTerm)> = monomials.into_iter()
            .map(|(c, exps)| {
                let pairs: Vec<(usize, usize)> = exps.into_iter()
                    .enumerate()
                    .filter(|(_, e)| *e > 0)
                    .collect();
                (c, SparseTerm::new(pairs))
            })
            .collect();
        Ok(Value::MVPoly(MVSparsePolynomial::from_coefficients_vec(num_vars, terms)))
    }
}

/// Interpret a sub-expression as a monomial: (coefficient, exponent_vector).
/// Variables from `ids` are formal indeterminates; everything else evaluates normally.
fn interpret_monomial(
    expr: &RecExpr<ArkLang>,
    id: Id,
    var_names: &[Symbol],
    num_vars: usize,
    env: &Env,
) -> Result<(Fr, Vec<usize>), EvalError> {
    match &expr[id] {
        ArkLang::Num(n) => {
            Ok((int_to_fr(*n), vec![0; num_vars]))
        }
        ArkLang::Symbol(s) => {
            if let Some(idx) = var_names.iter().position(|v| v == s) {
                let mut exps = vec![0usize; num_vars];
                exps[idx] = 1;
                Ok((Fr::one(), exps))
            } else {
                // Not a formal variable — evaluate from environment as a coefficient
                let v = eval_id(expr, id, env)?;
                let f = v.as_field().map_err(|_| EvalError::TypeError(
                    format!("poly: symbol '{}' is not a declared variable and could not be evaluated as a field element", s)
                ))?;
                Ok((f, vec![0; num_vars]))
            }
        }
        ArkLang::Pow([base, exp]) => {
            // base should be a variable symbol
            let base_node = &expr[*base];
            if let ArkLang::Symbol(s) = base_node {
                if let Some(idx) = var_names.iter().position(|v| v == s) {
                    // Evaluate exponent normally (supports expressions)
                    let exp_val = eval_id(expr, *exp, env)?.as_int()?;
                    if exp_val < 0 {
                        return Err(EvalError::TypeError(
                            format!("poly: negative exponent {} not allowed", exp_val)
                        ));
                    }
                    let mut exps = vec![0usize; num_vars];
                    exps[idx] = exp_val as usize;
                    return Ok((Fr::one(), exps));
                }
            }
            // If base is not a simple variable, fall through to normal eval
            let v = eval_id(expr, id, env)?;
            let f = v.as_field().map_err(|_| EvalError::TypeError(
                "poly: pow expression that is not (pow <var> <exp>) must evaluate to a field element".into()
            ))?;
            Ok((f, vec![0; num_vars]))
        }
        ArkLang::Mul([a, b]) => {
            let (ca, ea) = interpret_monomial(expr, *a, var_names, num_vars, env)?;
            let (cb, eb) = interpret_monomial(expr, *b, var_names, num_vars, env)?;
            let coeff = ca * cb;
            let exps: Vec<usize> = ea.iter().zip(eb.iter()).map(|(x, y)| x + y).collect();
            Ok((coeff, exps))
        }
        ArkLang::Neg([a]) => {
            let (ca, ea) = interpret_monomial(expr, *a, var_names, num_vars, env)?;
            Ok((-ca, ea))
        }
        ArkLang::Scale([c, m]) => {
            // c is a scalar coefficient, m is a monomial
            let cv = eval_id(expr, *c, env)?.as_field().map_err(|_|
                EvalError::TypeError("poly: scale coefficient must be a field element".into())
            )?;
            let (cm, em) = interpret_monomial(expr, *m, var_names, num_vars, env)?;
            Ok((cv * cm, em))
        }
        _ => {
            // Fall through: evaluate normally and treat as constant coefficient
            let v = eval_id(expr, id, env)?;
            let f = v.as_field().map_err(|_| EvalError::TypeError(
                format!("poly: unsupported term expression, evaluated to non-field value: {}", v.type_name())
            ))?;
            Ok((f, vec![0; num_vars]))
        }
    }
}

/// Specialize: replace all `(bound lo hi)` nodes with a concrete value.
///
/// Walks the expression tree and replaces every `Bound` node with `Num(value)`.
/// Panics if value is outside [lo, hi).
pub fn specialize(expr: &RecExpr<ArkLang>, var: Symbol, value: i64) -> RecExpr<ArkLang> {
    let nodes = expr.as_ref();
    let mut new_nodes: Vec<ArkLang> = Vec::with_capacity(nodes.len());
    // Find which Id the symbol `var` maps to (if any let-bound to a bound)
    // Strategy: walk all nodes. If a Let node binds `var` to a Bound, replace
    // the Bound with Num(value) and keep the rest unchanged.
    for node in nodes.iter() {
        new_nodes.push(node.clone());
    }
    // Find Let nodes that bind `var` to a Bound
    for i in 0..new_nodes.len() {
        if let ArkLang::Let([name_id, val_id, _body_id]) = &new_nodes[i] {
            // Check if name matches var
            if let ArkLang::Symbol(s) = &new_nodes[usize::from(*name_id)] {
                if *s == var {
                    // Check if val is a Bound node
                    let val_idx = usize::from(*val_id);
                    if let ArkLang::Bound([lo_id, hi_id]) = &new_nodes[val_idx] {
                        // Validate bounds
                        if let (ArkLang::Num(lo), ArkLang::Num(hi)) =
                            (&new_nodes[usize::from(*lo_id)], &new_nodes[usize::from(*hi_id)])
                        {
                            assert!(
                                value >= *lo && value < *hi,
                                "specialize: value {} outside bound [{}, {})",
                                value, lo, hi
                            );
                        }
                        // Replace the Bound node with Num(value)
                        new_nodes[val_idx] = ArkLang::Num(value);
                    }
                }
            }
        }
    }
    new_nodes.into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::G1Projective;
    use ark_ec::CurveGroup;
    use ark_ff::UniformRand;
    use ark_std::rand::SeedableRng;
    use rand::rngs::StdRng;

    fn empty_env() -> Env {
        HashMap::new()
    }

    fn eval_str(s: &str, env: &Env) -> Result<Value, EvalError> {
        let expr: RecExpr<ArkLang> = s.parse().expect("parse failed");
        eval(&expr, env)
    }

    // ── Field Arithmetic Tests ──

    #[test]
    fn test_field_add() {
        let v = eval_str("(add 3 7)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(10));
    }

    #[test]
    fn test_field_sub() {
        let v = eval_str("(add 10 (neg 3))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(7));
    }

    #[test]
    fn test_field_mul() {
        let v = eval_str("(mul 6 7)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn test_field_neg() {
        let v = eval_str("(add 5 (neg 5))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(0));
    }

    #[test]
    fn test_field_inv() {
        let v = eval_str("(mul 3 (inv 3))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(1));
    }

    #[test]
    fn test_field_div() {
        // 42 / 7 = 6: (mul 42 (inv 7))
        let v = eval_str("(mul 42 (inv 7))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(6));
    }

    #[test]
    fn test_field_inv_zero() {
        let r = eval_str("(inv 0)", &empty_env());
        assert!(matches!(r, Err(EvalError::DivisionByZero)));
    }

    #[test]
    fn test_field_pow() {
        let v = eval_str("(pow 2 10)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(1024));
    }

    #[test]
    fn test_field_additive_identity() {
        let v = eval_str("(add 42 0)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn test_field_multiplicative_identity() {
        let v = eval_str("(mul 42 1)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(42));
    }

    // ── Variable and Environment Tests ──

    #[test]
    fn test_variable_lookup() {
        let mut env = empty_env();
        env.insert("x".into(), Value::Field(Fr::from(42u64)));
        let v = eval_str("x", &env).unwrap();
        assert_eq!(v, Value::Field(Fr::from(42u64)));
    }

    #[test]
    fn test_unbound_variable() {
        let r = eval_str("x", &empty_env());
        assert!(matches!(r, Err(EvalError::UnboundVariable(_))));
    }

    // ── Let Binding Tests ──

    #[test]
    fn test_let_binding() {
        let v = eval_str("(let x 5 (mul x x))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(25));
    }

    #[test]
    fn test_let_nested() {
        let v = eval_str("(let x 3 (let y 4 (add (mul x x) (mul y y))))", &empty_env())
            .unwrap();
        assert_eq!(v, Value::Int(25));
    }

    // ── Conditional Tests ──

    #[test]
    fn test_if_true() {
        let v = eval_str("(if (eq 1 1) 42 0)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn test_if_false() {
        let v = eval_str("(if (eq 1 2) 42 0)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(0));
    }

    // ── Curve Operation Tests ──

    #[test]
    fn test_curve_add() {
        let mut rng = StdRng::seed_from_u64(1);
        let p = G1Projective::rand(&mut rng);
        let q = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("p".into(), Value::Curve(p));
        env.insert("q".into(), Value::Curve(q));

        let result = eval_str("(add p q)", &env).unwrap().as_curve().unwrap();
        assert_eq!(result.into_affine(), (p + q).into_affine());
    }

    #[test]
    fn test_curve_neg() {
        let mut rng = StdRng::seed_from_u64(2);
        let p = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("p".into(), Value::Curve(p));

        let result = eval_str("(add p (neg p))", &env).unwrap().as_curve().unwrap();
        assert!(result.is_zero());
    }

    #[test]
    fn test_scalar_mul() {
        let mut rng = StdRng::seed_from_u64(3);
        let p = G1Projective::rand(&mut rng);
        let s = Fr::from(7u64);
        let mut env = empty_env();
        env.insert("p".into(), Value::Curve(p));
        env.insert("s".into(), Value::Field(s));

        let result = eval_str("(scale s p)", &env).unwrap().as_curve().unwrap();
        assert_eq!(result.into_affine(), (p * s).into_affine());
    }

    #[test]
    fn test_scalar_mul_integer() {
        let mut rng = StdRng::seed_from_u64(4);
        let p = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("p".into(), Value::Curve(p));

        let result = eval_str("(scale 3 p)", &env).unwrap().as_curve().unwrap();
        let expected = p + p + p;
        assert_eq!(result.into_affine(), expected.into_affine());
    }

    // ── MSM via Σ Tests ──

    #[test]
    fn test_msm_via_sigma() {
        let mut rng = StdRng::seed_from_u64(30);
        let a = Fr::rand(&mut rng);
        let b = Fr::rand(&mut rng);
        let p = G1Projective::rand(&mut rng);
        let q = G1Projective::rand(&mut rng);

        let mut env = empty_env();
        env.insert("a".into(), Value::Field(a));
        env.insert("b".into(), Value::Field(b));
        env.insert("p".into(), Value::Curve(p));
        env.insert("q".into(), Value::Curve(q));

        // MSM([a,b], [P,Q]) = a*P + b*Q
        let result = eval_str(
            "(add (scale a p) (scale b q))", &env
        ).unwrap().as_curve().unwrap();

        let expected = p * a + q * b;
        assert_eq!(result.into_affine(), expected.into_affine());
    }

    // ── Polynomial Tests ──

    #[test]
    fn test_poly_eval() {
        let v = eval_str("(eval (poly:duv 1 2 3) 5)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(86));
    }

    #[test]
    fn test_poly_eval_constant() {
        let v = eval_str("(eval (poly:duv 42) 999)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn test_poly_add() {
        let v = eval_str("(eval (add (poly:duv 1 2) (poly:duv 3 4)) 10)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(64));
    }

    #[test]
    fn test_poly_mul() {
        let v = eval_str("(eval (mul (poly:duv 1 1) (poly:duv 1 1)) 3)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(16));
    }

    #[test]
    fn test_poly_sub() {
        let v = eval_str("(eval (add (poly:duv 1 2 3) (neg (poly:duv 1 2))) 2)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(12));
    }

    #[test]
    fn test_poly_neg() {
        let v = eval_str("(eval (add (poly:duv 1 1) (neg (poly:duv 1 1))) 7)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(0));
    }

    #[test]
    fn test_poly_div() {
        // pdiv now returns a Pair(quotient, remainder)
        let v = eval_str("(eval (fst (pdiv (poly:duv 1 3 2) (poly:duv 1 1))) 5)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(11));
    }

    #[test]
    fn test_poly_mod() {
        let v = eval_str("(eval (snd (pdiv (poly:duv 1 0 1) (poly:duv 1 1))) 999)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(2));
    }

    #[test]
    fn test_poly_deg() {
        let v = eval_str("(deg (poly:duv 1 2 3))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(2));
    }

    #[test]
    fn test_poly_scale() {
        let v = eval_str("(eval (scale 3 (poly:duv 1 1)) 2)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(9));
    }

    // ── MLE Tests ──

    #[test]
    fn test_mle_construct_and_eval() {
        let v = eval_str("(eval (poly:dmle 2 (mkarray 1 2 3 4)) (mkarray 0 0))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(1));

        let v = eval_str("(eval (poly:dmle 2 (mkarray 1 2 3 4)) (mkarray 1 0))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(2));
    }

    #[test]
    fn test_mle_nvars() {
        let v = eval_str("(nvars (poly:dmle 3 (mkarray 0 1 2 3 4 5 6 7)))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(3));
    }

    #[test]
    fn test_mle_fix_variables() {
        let v = eval_str(
            "(eval (fix (poly:dmle 2 (mkarray 1 2 3 4)) (mkarray 1)) (mkarray 0))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v, Value::Int(2));
    }

    #[test]
    fn test_mle_add() {
        let v = eval_str(
            "(eval (add (poly:dmle 2 (mkarray 1 0 0 0)) (poly:dmle 2 (mkarray 0 0 0 1))) (mkarray 0 0))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v, Value::Int(1));
    }

    // ── Multivariate Polynomial Tests ──

    #[test]
    fn test_mvpoly_construct_and_eval() {
        let v = eval_str(
            "(eval (poly:mv 2 (mkarray 5 2 3) (mkarray (mkarray) (mkarray 0 1) (mkarray 1 1))) (mkarray 2 7))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v, Value::Int(30));
    }

    #[test]
    fn test_mvpoly_degree() {
        let v = eval_str(
            "(deg (poly:mv 2 (mkarray 1) (mkarray (mkarray 0 2 1 1))))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v, Value::Int(3));
    }

    #[test]
    fn test_mvpoly_add() {
        let v = eval_str(
            "(eval (add (poly:mv 2 (mkarray 1 1) (mkarray (mkarray) (mkarray 0 1))) (poly:mv 2 (mkarray 2 1) (mkarray (mkarray) (mkarray 1 1)))) (mkarray 1 1))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v, Value::Int(5));
    }

    // ── Array Tests ──

    #[test]
    fn test_array_create_and_select() {
        let v = eval_str("(select (mkarray 10 20 30) 1)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(20));
    }

    #[test]
    fn test_array_len() {
        let v = eval_str("(alen (mkarray 1 2 3 4 5))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(5));
    }

    #[test]
    fn test_array_index_out_of_bounds() {
        let r = eval_str("(select (mkarray 1 2) 5)", &empty_env());
        assert!(matches!(r, Err(EvalError::IndexOutOfBounds { .. })));
    }

    #[test]
    fn test_store_basic() {
        let v = eval_str("(select (store (mkarray 1 2 3) 1 99) 1)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(99));
    }

    #[test]
    fn test_store_preserves_other() {
        let v = eval_str("(select (store (mkarray 1 2 3) 1 99) 0)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(1));
    }

    #[test]
    fn test_store_out_of_bounds() {
        let r = eval_str("(store (mkarray 1 2 3) 5 99)", &empty_env());
        assert!(matches!(r, Err(EvalError::IndexOutOfBounds { .. })));
    }

    #[test]
    fn test_alen_after_store() {
        let v = eval_str("(alen (store (mkarray 1 2 3) 0 99))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(3));
    }

    #[test]
    fn test_store_type_mismatch() {
        let mut rng = StdRng::seed_from_u64(100);
        let p = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("p".into(), Value::Curve(p));
        let r = eval_str("(store (mkarray 1 2 3) 0 p)", &env);
        assert!(matches!(r, Err(EvalError::TypeMismatch { .. })));
    }

    // ── Complex Expression Tests ──

    #[test]
    fn test_nested_field_expression() {
        // (3 + 4) * (5 - 2) = 7 * 3 = 21
        let v = eval_str("(mul (add 3 4) (add 5 (neg 2)))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(21));
    }

    #[test]
    fn test_horner_form() {
        let mut env = empty_env();
        env.insert("x".into(), Value::Int(5));
        let v = eval_str("(add 1 (mul x (add 2 (mul x 3))))", &env).unwrap();
        assert_eq!(v, Value::Int(86));
    }

    #[test]
    fn test_polynomial_vs_horner_equivalence() {
        let mut env = empty_env();
        env.insert("x".into(), Value::Int(7));

        let poly_result = eval_str("(eval (poly:duv 5 3 2 1) x)", &env)
            .unwrap()
            .as_field()
            .unwrap();
        let horner_result = eval_str(
            "(add 5 (mul x (add 3 (mul x (add 2 (mul x 1))))))",
            &env,
        )
        .unwrap()
        .as_field()
        .unwrap();
        assert_eq!(poly_result, horner_result);
    }

    // ── Sparse UV Polynomial Tests ──

    #[test]
    fn test_sparse_uv_poly_eval() {
        let v = eval_str("(eval (poly:suv 0 5 2 3) 2)", &empty_env()).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(17u64));
    }

    #[test]
    fn test_sparse_uv_single_term() {
        let v = eval_str("(eval (poly:suv 3 7) 2)", &empty_env()).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(56u64));
    }

    // ── Sparse MLE Tests ──

    #[test]
    fn test_sparse_mle_eval() {
        let v = eval_str(
            "(eval (poly:smle 2 (mkarray 0 10 3 20)) (mkarray 0 0))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(10u64));
    }

    #[test]
    fn test_sparse_mle_eval_at_one_one() {
        let v = eval_str(
            "(eval (poly:smle 2 (mkarray 0 10 3 20)) (mkarray 1 1))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(20u64));
    }

    // ── Sigma/Pi Tests ──

    #[test]
    fn test_sigma_sum() {
        let v = eval_str("(Σ i 0 3 (select (mkarray 10 20 30) i))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(60));
    }

    #[test]
    fn test_sigma_scale() {
        let mut rng = StdRng::seed_from_u64(50);
        let p0 = G1Projective::rand(&mut rng);
        let p1 = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("P0".into(), Value::Curve(p0));
        env.insert("P1".into(), Value::Curve(p1));

        let result = eval_str(
            "(Σ i 0 2 (scale (select (mkarray 3 5) i) (select (mkarray P0 P1) i)))",
            &env,
        ).unwrap().as_curve().unwrap();

        let expected = p0 * Fr::from(3u64) + p1 * Fr::from(5u64);
        assert_eq!(result.into_affine(), expected.into_affine());
    }

    #[test]
    fn test_pi_product() {
        let v = eval_str("(Π i 0 3 (select (mkarray 2 3 5) i))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(30));
    }

    #[test]
    fn test_bound_error() {
        let r = eval_str("(bound 2 100)", &empty_env());
        assert!(matches!(r, Err(EvalError::TypeError(ref msg)) if msg.contains("cannot evaluate symbolic bound")));
    }

    #[test]
    fn test_sigma_empty_range() {
        let v = eval_str("(Σ i 5 3 42)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(0));
    }

    #[test]
    fn test_pi_empty_range() {
        let v = eval_str("(Π i 5 3 42)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(1));
    }

    // ── Conversion Tests ──

    #[test]
    fn test_densify_sparse_uv() {
        // Create sparse poly 5 + 3x^2, densify, evaluate
        let v = eval_str("(eval (densify (poly:suv 0 5 2 3)) 2)", &empty_env()).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(17u64));
    }

    #[test]
    fn test_sparsify_dense_uv() {
        // Create dense poly [5, 0, 3] (5 + 3x^2), sparsify, evaluate
        let v = eval_str("(eval (sparsify (poly:duv 5 0 3)) 2)", &empty_env()).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(17u64));
    }

    #[test]
    fn test_as_uv_mle() {
        // 1-var MLE with evals [3, 7]: linear poly f(x) = 3 + 4x
        // Evaluate at x=2: 3 + 8 = 11
        let v = eval_str("(eval (as-uv (poly:dmle 1 (mkarray 3 7))) 2)", &empty_env()).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(11u64));
    }

    #[test]
    fn test_as_mle_uv() {
        // UV poly [3, 4] (3 + 4x) → MLE with 1 var
        // Eval at (0) → 3, eval at (1) → 7
        let v0 = eval_str("(eval (as-mle (poly:duv 3 4)) (mkarray 0))", &empty_env()).unwrap();
        assert_eq!(v0.as_field().unwrap(), Fr::from(3u64));
        let v1 = eval_str("(eval (as-mle (poly:duv 3 4)) (mkarray 1))", &empty_env()).unwrap();
        assert_eq!(v1.as_field().unwrap(), Fr::from(7u64));
    }

    // ── Staging Pipeline Tests ──

    #[test]
    fn test_specialize_bound() {
        // Build: (let N (bound 2 100) (Σ i 0 N (select (mkarray 10 20 30) i)))
        // Specialize N=3
        // Should evaluate to 10+20+30 = 60
        let expr: RecExpr<ArkLang> =
            "(let N (bound 2 100) (Σ i 0 N (select (mkarray 10 20 30) i)))".parse().unwrap();
        let specialized = specialize(&expr, "N".into(), 3);
        let result = eval(&specialized, &empty_env()).unwrap();
        assert_eq!(result.as_field().unwrap(), Fr::from(60u64));
    }

    #[test]
    fn test_specialize_msm_pattern() {
        // Parametric MSM: (let N (bound 1 10) (Σ i 0 N (scale (select s i) (select P i))))
        // Specialize N=2 with concrete scalars and points
        let mut rng = StdRng::seed_from_u64(42);
        let p0 = G1Projective::rand(&mut rng);
        let p1 = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("s".into(), Value::Array(vec![Value::Int(3), Value::Int(5)]));
        env.insert("P".into(), Value::Array(vec![Value::Curve(p0), Value::Curve(p1)]));

        let expr: RecExpr<ArkLang> =
            "(let N (bound 1 10) (Σ i 0 N (scale (select s i) (select P i))))".parse().unwrap();
        let specialized = specialize(&expr, "N".into(), 2);
        let result = eval(&specialized, &env).unwrap().as_curve().unwrap();

        // Expected: 3*P0 + 5*P1
        use ark_ec::CurveGroup;
        let expected = p0 * Fr::from(3u64) + p1 * Fr::from(5u64);
        assert_eq!(result.into_affine(), expected.into_affine());
    }

    #[test]
    #[should_panic(expected = "specialize: value 200 outside bound [2, 100)")]
    fn test_specialize_out_of_bounds() {
        let expr: RecExpr<ArkLang> =
            "(let N (bound 2 100) N)".parse().unwrap();
        let _ = specialize(&expr, "N".into(), 200);
    }

    // ── FFT / Domain Tests ──

    #[test]
    fn test_domain_elements() {
        // Domain of size 4: should be [1, ω, ω², ω³] where ω^4 = 1
        let v = eval_str("(domain 4)", &empty_env()).unwrap();
        let arr = v.as_array().unwrap();
        assert_eq!(arr.len(), 4);
        // First element is always 1 (ω^0)
        assert_eq!(arr[0].as_field().unwrap(), Fr::from(1u64));
        // ω^4 should equal 1: check that element^4 = 1
        let omega = arr[1].as_field().unwrap();
        let mut omega4 = omega;
        for _ in 1..4 { omega4 *= omega; }
        assert_eq!(omega4, Fr::from(1u64));
    }

    #[test]
    fn test_fft_known_poly() {
        // FFT of constant polynomial [5] over domain size 4
        // All evaluations should be 5
        let v = eval_str("(fft 4 (poly:duv 5))", &empty_env()).unwrap();
        let arr = v.as_array().unwrap();
        assert_eq!(arr.len(), 4);
        for elem in &arr {
            assert_eq!(elem.as_field().unwrap(), Fr::from(5u64));
        }
    }

    #[test]
    fn test_fft_linear_poly() {
        // FFT of p(x) = 1 + 2x over domain of size 4
        // Evaluations at [1, ω, ω², ω³] = [1+2·1, 1+2ω, 1+2ω², 1+2ω³]
        let env = empty_env();
        let evals = eval_str("(fft 4 (poly:duv 1 2))", &env).unwrap().as_array().unwrap();
        let domain_pts = eval_str("(domain 4)", &env).unwrap().as_array().unwrap();
        for i in 0..4 {
            let omega_i = domain_pts[i].as_field().unwrap();
            let expected = Fr::from(1u64) + Fr::from(2u64) * omega_i;
            assert_eq!(evals[i].as_field().unwrap(), expected);
        }
    }

    #[test]
    fn test_ifft_roundtrip() {
        // ifft(fft(p)) should recover p
        let env = empty_env();
        let original = eval_str("(eval (poly:duv 3 5 7) 42)", &env).unwrap().as_field().unwrap();
        let recovered = eval_str("(eval (ifft 4 (fft 4 (poly:duv 3 5 7))) 42)", &env).unwrap().as_field().unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn test_fft_from_array() {
        // FFT should accept Array[Field] as raw coefficients
        let env = empty_env();
        let from_poly = eval_str("(fft 4 (poly:duv 1 2 3))", &env).unwrap();
        let from_arr = eval_str("(fft 4 (mkarray 1 2 3))", &env).unwrap();
        assert_eq!(from_poly, from_arr);
    }

    #[test]
    fn test_fft_from_sparse() {
        // FFT should accept SparseUVPoly
        let env = empty_env();
        let from_dense = eval_str("(fft 4 (poly:duv 5 0 3))", &env).unwrap();
        let from_sparse = eval_str("(fft 4 (poly:suv 0 5 2 3))", &env).unwrap();
        assert_eq!(from_dense, from_sparse);
    }

    #[test]
    fn test_fft_eval_matches_point_eval() {
        // FFT evaluations should match point-by-point eval at domain elements
        let env = empty_env();
        let evals = eval_str("(fft 8 (poly:duv 1 2 3 4))", &env).unwrap().as_array().unwrap();
        let domain_pts = eval_str("(domain 8)", &env).unwrap().as_array().unwrap();
        for i in 0..8 {
            let pt = domain_pts[i].as_field().unwrap();
            let mut env2 = empty_env();
            env2.insert("x".into(), Value::Field(pt));
            let point_eval = eval_str("(eval (poly:duv 1 2 3 4) x)", &env2).unwrap().as_field().unwrap();
            assert_eq!(evals[i].as_field().unwrap(), point_eval);
        }
    }

    // ── Symbolic Polynomial Constructor Tests ──

    #[test]
    fn test_poly_univariate_basic() {
        // (poly (ids x) (mul 3 (pow x 2)) (mul 5 x) 7) = 3x² + 5x + 7
        let env = empty_env();
        let v = eval_str("(eval (poly (ids x) (mul 3 (pow x 2)) (mul 5 x) 7) 2)", &env).unwrap();
        // 3*4 + 5*2 + 7 = 12 + 10 + 7 = 29
        assert_eq!(v.as_field().unwrap(), Fr::from(29u64));
    }

    #[test]
    fn test_poly_univariate_matches_suv() {
        // (poly (ids x) (mul 3 (pow x 2)) (mul 5 x) 7) should match (poly:suv 0 7 1 5 2 3)
        let env = empty_env();
        let from_sym = eval_str("(eval (poly (ids x) (mul 3 (pow x 2)) (mul 5 x) 7) 10)", &env).unwrap();
        let from_suv = eval_str("(eval (poly:suv 0 7 1 5 2 3) 10)", &env).unwrap();
        assert_eq!(from_sym.as_field().unwrap(), from_suv.as_field().unwrap());
    }

    #[test]
    fn test_poly_bare_variable() {
        // (poly (ids x) x) = x
        let env = empty_env();
        let v = eval_str("(eval (poly (ids x) x) 42)", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(42u64));
    }

    #[test]
    fn test_poly_constant() {
        // (poly (ids x) 5) = constant polynomial 5
        let env = empty_env();
        let v = eval_str("(eval (poly (ids x) 5) 99)", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(5u64));
    }

    #[test]
    fn test_poly_negative_coeff() {
        // (poly (ids x) (neg (pow x 2)) x) = -x² + x
        let env = empty_env();
        let v = eval_str("(eval (poly (ids x) (neg (pow x 2)) x) 3)", &env).unwrap();
        // -9 + 3 = -6 in the field
        let expected = -Fr::from(9u64) + Fr::from(3u64);
        assert_eq!(v.as_field().unwrap(), expected);
    }

    #[test]
    fn test_poly_multivariate() {
        // (poly (ids x y) (pow x 2) (pow y 3) 4) = x² + y³ + 4
        let env = empty_env();
        let v = eval_str(
            "(eval (poly (ids x y) (pow x 2) (pow y 3) 4) (mkarray 3 2))",
            &env,
        ).unwrap();
        // 9 + 8 + 4 = 21
        assert_eq!(v.as_field().unwrap(), Fr::from(21u64));
    }

    #[test]
    fn test_poly_multivariate_cross_term() {
        // (poly (ids x y) (mul 2 (mul x y))) = 2xy
        let env = empty_env();
        let v = eval_str(
            "(eval (poly (ids x y) (mul 2 (mul x y))) (mkarray 3 5))",
            &env,
        ).unwrap();
        // 2*3*5 = 30
        assert_eq!(v.as_field().unwrap(), Fr::from(30u64));
    }

    #[test]
    fn test_poly_env_exponent() {
        // (poly (ids x) (pow x n)) where n comes from environment
        let mut env = empty_env();
        env.insert("n".into(), Value::Int(3));
        let v = eval_str("(eval (poly (ids x) (pow x n)) 2)", &env).unwrap();
        // 2³ = 8
        assert_eq!(v.as_field().unwrap(), Fr::from(8u64));
    }

    #[test]
    fn test_poly_env_coefficient() {
        // (poly (ids x) (mul c (pow x 2))) where c comes from environment
        let mut env = empty_env();
        env.insert("c".into(), Value::Field(Fr::from(7u64)));
        let v = eval_str("(eval (poly (ids x) (mul c (pow x 2))) 3)", &env).unwrap();
        // 7*9 = 63
        assert_eq!(v.as_field().unwrap(), Fr::from(63u64));
    }

    // ── Tuple Tests ──

    #[test]
    fn test_pair_fst_snd() {
        let env = empty_env();
        let v = eval_str("(fst (pair 3 7))", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(3u64));
        let v = eval_str("(snd (pair 3 7))", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(7u64));
    }

    #[test]
    fn test_pair_nested() {
        let env = empty_env();
        let v = eval_str("(fst (snd (pair 1 (pair 2 3))))", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(2u64));
    }

    #[test]
    fn test_pdiv_returns_pair() {
        let env = empty_env();
        // (2x² + 3x + 1) / (x + 1) = quotient (2x + 1), remainder 0
        let q = eval_str("(eval (fst (pdiv (poly:duv 1 3 2) (poly:duv 1 1))) 5)", &env).unwrap();
        assert_eq!(q.as_field().unwrap(), Fr::from(11u64));
        let r = eval_str("(eval (snd (pdiv (poly:duv 1 3 2) (poly:duv 1 1))) 5)", &env).unwrap();
        assert_eq!(r.as_field().unwrap(), Fr::from(0u64));
    }

    #[test]
    fn test_pdiv_division_identity() {
        // a = q*b + r: (x² + 1) / (x + 1) → q = x - 1, r = 2
        // Verify: q*b + r = a at x = 5
        let env = empty_env();
        let a_val = eval_str("(eval (poly:duv 1 0 1) 5)", &env).unwrap().as_field().unwrap();
        let q_val = eval_str("(eval (fst (pdiv (poly:duv 1 0 1) (poly:duv 1 1))) 5)", &env).unwrap().as_field().unwrap();
        let b_val = eval_str("(eval (poly:duv 1 1) 5)", &env).unwrap().as_field().unwrap();
        let r_val = eval_str("(eval (snd (pdiv (poly:duv 1 0 1) (poly:duv 1 1))) 5)", &env).unwrap().as_field().unwrap();
        assert_eq!(a_val, q_val * b_val + r_val);
    }

    // ── Array Addition Tests ──

    #[test]
    fn test_aadd_basic() {
        let env = empty_env();
        let v = eval_str("(aadd (mkarray 1 2 3) (mkarray 4 5 6))", &env).unwrap().as_array().unwrap();
        assert_eq!(v.len(), 3);
        assert_eq!(v[0].as_field().unwrap(), Fr::from(5u64));
        assert_eq!(v[1].as_field().unwrap(), Fr::from(7u64));
        assert_eq!(v[2].as_field().unwrap(), Fr::from(9u64));
    }

    #[test]
    fn test_aadd_different_lengths() {
        let env = empty_env();
        let v = eval_str("(aadd (mkarray 1 2) (mkarray 10 20 30))", &env).unwrap().as_array().unwrap();
        assert_eq!(v.len(), 3);
        assert_eq!(v[0].as_field().unwrap(), Fr::from(11u64));
        assert_eq!(v[1].as_field().unwrap(), Fr::from(22u64));
        assert_eq!(v[2].as_field().unwrap(), Fr::from(30u64));
    }

    #[test]
    fn test_aadd_empty() {
        let env = empty_env();
        let v = eval_str("(aadd (mkarray) (mkarray 1 2))", &env).unwrap().as_array().unwrap();
        assert_eq!(v.len(), 2);
        assert_eq!(v[0].as_field().unwrap(), Fr::from(1u64));
    }
}
