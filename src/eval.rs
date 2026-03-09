// arkΣΠ Runtime Evaluator
//
// Recursively evaluates a RecExpr<ArkLang> against arkworks types.
// Uses typed dispatch functions for arithmetic operations.

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

use crate::language::{ArkLang, tag_to_type};
use crate::value::{ArkType, EvalError, Value, check_homogeneous, int_to_fr};

/// Environment mapping variable names to values.
pub type Env = HashMap<Symbol, Value>;

/// Evaluate an arkΣΠ expression with the given environment.
pub fn eval(expr: &RecExpr<ArkLang>, env: &Env) -> Result<Value, EvalError> {
    let root = Id::from(expr.as_ref().len() - 1);
    eval_id(expr, root, env)
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

        // ── Compound Type Tag (not directly evaluable) ──
        ArkLang::ArrayOf(_) => {
            Err(EvalError::TypeError("arrayof is a type tag, not an expression".into()))
        }

        // ── Symbolic MLE Constructor (placeholder) ──
        ArkLang::Mle(_) => {
            Err(EvalError::TypeError("mle: not yet implemented".into()))
        }

        // ── Symbolic Polynomial Constructor ──
        ArkLang::Poly(children) => {
            eval_symbolic_poly(expr, children, env)
        }
        ArkLang::Ids(_) => {
            Err(EvalError::TypeError("ids: cannot be evaluated standalone, use inside (poly ...)".into()))
        }

        // ── Poly-Specific: Fix ──
        ArkLang::Fix(_) => {
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

        // ── Domain ──
        ArkLang::Domain([n]) => {
            let size = eval_id(expr, *n, env)?.as_int()? as usize;
            let domain = GeneralEvaluationDomain::<Fr>::new(size)
                .ok_or_else(|| EvalError::TypeError(format!(
                    "domain: cannot create evaluation domain of size {}", size
                )))?;
            let elements: Vec<Value> = domain.elements().map(Value::Field).collect();
            Ok(Value::Array(elements))
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
                    Some(prev) => typed_add(prev.ark_type(), val.ark_type(), prev, val)?,
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
                    Some(prev) => typed_mul(prev.ark_type(), val.ark_type(), prev, val)?,
                });
            }
            Ok(acc.unwrap_or(Value::Int(1)))
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

        ArkLang::Length([arr]) => {
            let va = eval_id(expr, *arr, env)?.as_array()?;
            Ok(Value::Int(va.len() as i64))
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

        // ── Type Tags (not directly evaluable) ──
        ArkLang::TField | ArkLang::TCurve | ArkLang::TInt | ArkLang::TBool
        | ArkLang::TDensePoly | ArkLang::TSparsePoly | ArkLang::TDenseMLE
        | ArkLang::TSparseMLE | ArkLang::TMVPoly | ArkLang::TArray | ArkLang::TPair => {
            Err(EvalError::TypeError("type tags cannot be evaluated directly".into()))
        }

        // ── Coerce ──
        ArkLang::Coerce([src, dst, x]) => {
            let src_ty = resolve_type_tag(expr, *src)?;
            let dst_ty = resolve_type_tag(expr, *dst)?;
            let val = eval_id(expr, *x, env)?;
            validate_type(&val, &src_ty)?;
            eval_coerce(src_ty, dst_ty, val)
        }

        // ── Typed Add ──
        ArkLang::Add([ta, tb, a, b]) => {
            let ty_a = resolve_type_tag(expr, *ta)?;
            let ty_b = resolve_type_tag(expr, *tb)?;
            let va = eval_id(expr, *a, env)?;
            let vb = eval_id(expr, *b, env)?;
            validate_type(&va, &ty_a)?;
            validate_type(&vb, &ty_b)?;
            typed_add(ty_a, ty_b, va, vb)
        }

        // ── Typed Neg ──
        ArkLang::Neg([t, a]) => {
            let ty = resolve_type_tag(expr, *t)?;
            let va = eval_id(expr, *a, env)?;
            validate_type(&va, &ty)?;
            typed_neg(ty, va)
        }

        // ── Typed Mul ──
        ArkLang::Mul([ta, tb, a, b]) => {
            let ty_a = resolve_type_tag(expr, *ta)?;
            let ty_b = resolve_type_tag(expr, *tb)?;
            let va = eval_id(expr, *a, env)?;
            let vb = eval_id(expr, *b, env)?;
            validate_type(&va, &ty_a)?;
            validate_type(&vb, &ty_b)?;
            typed_mul(ty_a, ty_b, va, vb)
        }

        // ── Typed Inv ──
        ArkLang::Inv([t, a]) => {
            let ty = resolve_type_tag(expr, *t)?;
            let va = eval_id(expr, *a, env)?;
            validate_type(&va, &ty)?;
            match ty {
                ArkType::Field => {
                    let f = va.as_field()?;
                    f.inverse().map(Value::Field).ok_or(EvalError::DivisionByZero)
                }
                _ => Err(EvalError::TypeError(format!("inv: only Field supported, got {:?}", ty))),
            }
        }

        // ── Typed Pow ──
        ArkLang::Pow([t, base, exp]) => {
            let ty = resolve_type_tag(expr, *t)?;
            let vb = eval_id(expr, *base, env)?;
            validate_type(&vb, &ty)?;
            let ve = eval_id(expr, *exp, env)?;
            validate_type(&ve, &ArkType::Int)?;
            match ty {
                ArkType::Field => {
                    let b = vb.as_field()?;
                    let e = ve.as_int()?;
                    if e >= 0 {
                        let mut result = Fr::from(1u64);
                        for _ in 0..e { result *= b; }
                        Ok(Value::Field(result))
                    } else {
                        let inv = b.inverse().ok_or(EvalError::DivisionByZero)?;
                        let mut result = Fr::from(1u64);
                        for _ in 0..(-e) { result *= inv; }
                        Ok(Value::Field(result))
                    }
                }
                _ => Err(EvalError::TypeError(format!("pow: only Field supported, got {:?}", ty))),
            }
        }

        // ── Typed Eval ──
        ArkLang::Eval([t, p, x]) => {
            let ty = resolve_type_tag(expr, *t)?;
            let vp = eval_id(expr, *p, env)?;
            validate_type(&vp, &ty)?;
            match vp {
                Value::Polynomial(poly) => {
                    let xv = eval_id(expr, *x, env)?.as_field()?;
                    Ok(Value::Field(poly.evaluate(&xv)))
                }
                Value::SparseUVPoly(sp) => {
                    let xv = eval_id(expr, *x, env)?.as_field()?;
                    Ok(Value::Field(Polynomial::evaluate(&sp, &xv)))
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
                _ => Err(EvalError::TypeError(format!(
                    "eval: unsupported type {:?}", ty
                ))),
            }
        }

        // ── Typed Deg ──
        ArkLang::Deg([t, p]) => {
            let ty = resolve_type_tag(expr, *t)?;
            let vp = eval_id(expr, *p, env)?;
            validate_type(&vp, &ty)?;
            match vp {
                Value::Polynomial(p) => Ok(Value::Int(p.degree() as i64)),
                Value::SparseUVPoly(p) => Ok(Value::Int(p.degree() as i64)),
                Value::MVPoly(p) => Ok(Value::Int(p.degree() as i64)),
                Value::MLE(m) => Ok(Value::Int(m.num_vars() as i64)),
                Value::SparseMLE(m) => Ok(Value::Int(m.num_vars() as i64)),
                _ => Err(EvalError::TypeError(format!(
                    "deg: unsupported type {:?}", ty
                ))),
            }
        }

        // ── Typed NVars ──
        ArkLang::NVars([t, p]) => {
            let ty = resolve_type_tag(expr, *t)?;
            let vp = eval_id(expr, *p, env)?;
            validate_type(&vp, &ty)?;
            match vp {
                Value::MLE(m) => Ok(Value::Int(m.num_vars() as i64)),
                Value::SparseMLE(m) => Ok(Value::Int(m.num_vars() as i64)),
                Value::MVPoly(p) => Ok(Value::Int(p.num_vars() as i64)),
                Value::Polynomial(_) | Value::SparseUVPoly(_) => Ok(Value::Int(1)),
                _ => Err(EvalError::TypeError(format!(
                    "nvars: unsupported type {:?}", ty
                ))),
            }
        }

        // ── Typed Div ──
        ArkLang::Div([t, a, b]) => {
            let ty = resolve_type_tag(expr, *t)?;
            if ty != ArkType::DensePoly {
                return Err(EvalError::TypeError(format!(
                    "div: only DensePoly supported, got {:?}", ty
                )));
            }
            let va = eval_id(expr, *a, env)?;
            validate_type(&va, &ty)?;
            let vb = eval_id(expr, *b, env)?;
            validate_type(&vb, &ty)?;
            let pa = va.as_polynomial()?;
            let pb = vb.as_polynomial()?;
            if pb.is_zero() {
                return Err(EvalError::DivisionByZero);
            }
            let a_sparse = DenseOrSparsePolynomial::from(&pa);
            let b_sparse = DenseOrSparsePolynomial::from(&pb);
            let (q, r) = a_sparse.divide_with_q_and_r(&b_sparse)
                .ok_or(EvalError::DivisionByZero)?;
            Ok(Value::Pair(Box::new(Value::Polynomial(q)), Box::new(Value::Polynomial(r))))
        }

        // ── Typed FFT ──
        ArkLang::Fft([t, n, p]) => {
            let ty = resolve_type_tag(expr, *t)?;
            let size = eval_id(expr, *n, env)?.as_int()? as usize;
            let domain = GeneralEvaluationDomain::<Fr>::new(size)
                .ok_or_else(|| EvalError::TypeError(format!(
                    "fft: cannot create evaluation domain of size {}", size
                )))?;
            let vp = eval_id(expr, *p, env)?;
            validate_type(&vp, &ty)?;
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
                _ => return Err(EvalError::TypeError(format!(
                    "fft: expected polynomial or array, got {:?}", ty
                ))),
            };
            let evals = domain.fft(&coeffs);
            Ok(Value::Array(evals.into_iter().map(Value::Field).collect()))
        }

        // ── Typed IFFT ──
        ArkLang::Ifft([t, n, e]) => {
            let ty = resolve_type_tag(expr, *t)?;
            if ty != ArkType::Array {
                return Err(EvalError::TypeError(format!(
                    "ifft: expected Array type tag, got {:?}", ty
                )));
            }
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
            let mut trimmed = coeffs;
            while trimmed.len() > 1 && trimmed.last().map_or(false, |c| c.is_zero()) {
                trimmed.pop();
            }
            Ok(Value::Polynomial(DensePolynomial::from_coefficients_vec(trimmed)))
        }

        // ── Typed Get ──
        ArkLang::Get([_t, arr, idx]) => {
            // Type tag describes element type — validated post-hoc
            let va = eval_id(expr, *arr, env)?.as_array()?;
            let vi = eval_id(expr, *idx, env)?.as_int()?;
            let i = vi as usize;
            if i >= va.len() {
                return Err(EvalError::IndexOutOfBounds {
                    index: i,
                    len: va.len(),
                });
            }
            Ok(va[i].clone())
        }

        // ── Typed Set ──
        ArkLang::Set([_t, arr, idx, val]) => {
            let mut va = eval_id(expr, *arr, env)?.as_array()?;
            let vi = eval_id(expr, *idx, env)?.as_int()?;
            let vv = eval_id(expr, *val, env)?;
            let i = vi as usize;
            if i >= va.len() {
                return Err(EvalError::IndexOutOfBounds {
                    index: i,
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
            va[i] = vv;
            Ok(Value::Array(va))
        }

        // ── Typed Eq ──
        ArkLang::Eq([t, a, b]) => {
            let ty = resolve_type_tag(expr, *t)?;
            let va = eval_id(expr, *a, env)?;
            validate_type(&va, &ty)?;
            let vb = eval_id(expr, *b, env)?;
            validate_type(&vb, &ty)?;
            match ty {
                ArkType::Field | ArkType::Int => {
                    let fa = va.as_field()?;
                    let fb = vb.as_field()?;
                    Ok(Value::Bool(fa == fb))
                }
                ArkType::Bool => {
                    let ba = va.as_bool()?;
                    let bb = vb.as_bool()?;
                    Ok(Value::Bool(ba == bb))
                }
                _ => Err(EvalError::TypeError(format!(
                    "eq: unsupported type {:?}", ty
                ))),
            }
        }
    }
}

/// Resolve a type-tag AST node to its ArkType.
fn resolve_type_tag(expr: &RecExpr<ArkLang>, id: Id) -> Result<ArkType, EvalError> {
    // Handle compound type tags like (arrayof T)
    if let ArkLang::ArrayOf([inner]) = &expr[id] {
        let elem_ty = resolve_type_tag(expr, *inner)?;
        return Ok(ArkType::ArrayOf(Box::new(elem_ty)));
    }
    tag_to_type(&expr[id]).ok_or_else(|| {
        EvalError::TypeError(format!(
            "expected a type tag (Field, Curve, Int, ..., (arrayof T)), got {:?}",
            expr[id]
        ))
    })
}

/// Validate that a runtime value matches the expected type tag.
fn validate_type(val: &Value, expected: &ArkType) -> Result<(), EvalError> {
    let actual = val.ark_type();
    if actual == *expected {
        Ok(())
    } else if actual == ArkType::Int && *expected == ArkType::Field {
        // Int auto-coerces to Field (via as_field())
        Ok(())
    } else if matches!(expected, ArkType::ArrayOf(_)) && actual == ArkType::Array {
        // ArrayOf(T) accepts any Array value (element types checked at use site)
        Ok(())
    } else {
        Err(EvalError::TypeMismatch {
            expected: format!("{:?}", expected),
            got: format!("{:?} ({})", actual, val.type_name()),
        })
    }
}

/// Perform an explicit type coercion.
fn eval_coerce(src: ArkType, dst: ArkType, val: Value) -> Result<Value, EvalError> {
    use ArkType::*;
    match (&src, &dst) {
        // Identity
        (s, d) if s == d => Ok(val),

        // ── Embedding: Int → Field ──
        (Int, Field) => {
            let n = val.as_int()?;
            Ok(Value::Field(int_to_fr(n)))
        }

        // ── Embedding: Int → polynomial types (via Field) ──
        (Int, DensePoly) => {
            let n = val.as_int()?;
            let c = int_to_fr(n);
            Ok(Value::Polynomial(DensePolynomial::from_coefficients_vec(vec![c])))
        }
        (Int, SparsePoly) => {
            let n = val.as_int()?;
            let c = int_to_fr(n);
            if c.is_zero() {
                Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(vec![])))
            } else {
                Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(vec![(0, c)])))
            }
        }
        (Int, DenseMLE) => {
            let n = val.as_int()?;
            let c = int_to_fr(n);
            Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(1, vec![c, c])))
        }
        (Int, SparseMLE) => {
            let n = val.as_int()?;
            let c = int_to_fr(n);
            let evals = if c.is_zero() { vec![] } else { vec![(0, c), (1, c)] };
            Ok(Value::SparseMLE(SparseMultilinearExtension::from_evaluations(1, &evals)))
        }
        (Int, MVPoly) => {
            let n = val.as_int()?;
            let c = int_to_fr(n);
            Ok(Value::MVPoly(MVSparsePolynomial::from_coefficients_vec(
                1, vec![(c, SparseTerm::new(vec![]))]
            )))
        }

        // ── Embedding: Field → polynomial types ──
        (Field, DensePoly) => {
            let c = val.as_field()?;
            Ok(Value::Polynomial(DensePolynomial::from_coefficients_vec(vec![c])))
        }
        (Field, SparsePoly) => {
            let c = val.as_field()?;
            if c.is_zero() {
                Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(vec![])))
            } else {
                Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(vec![(0, c)])))
            }
        }
        (Field, DenseMLE) => {
            let c = val.as_field()?;
            Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(1, vec![c, c])))
        }
        (Field, SparseMLE) => {
            let c = val.as_field()?;
            let evals = if c.is_zero() { vec![] } else { vec![(0, c), (1, c)] };
            Ok(Value::SparseMLE(SparseMultilinearExtension::from_evaluations(1, &evals)))
        }
        (Field, MVPoly) => {
            let c = val.as_field()?;
            Ok(Value::MVPoly(MVSparsePolynomial::from_coefficients_vec(
                1, vec![(c, SparseTerm::new(vec![]))]
            )))
        }

        // ── Representation change: Dense ↔ Sparse (univariate) ──
        (SparsePoly, DensePoly) => {
            // was: densify for SparseUVPoly
            let p = val.as_sparse_uv_poly()?;
            let deg = p.degree();
            let mut coeffs = vec![Fr::zero(); deg + 1];
            for (i, c) in p.to_vec().iter() {
                if *i <= deg { coeffs[*i] = *c; }
            }
            Ok(Value::Polynomial(DensePolynomial::from_coefficients_vec(coeffs)))
        }
        (DensePoly, SparsePoly) => {
            // was: sparsify for DensePolynomial
            let p = val.as_polynomial()?;
            let sparse_coeffs: Vec<(usize, Fr)> = p.coeffs.iter()
                .enumerate()
                .filter(|(_, c)| !c.is_zero())
                .map(|(i, c)| (i, *c))
                .collect();
            Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(sparse_coeffs)))
        }

        // ── Representation change: Dense ↔ Sparse (MLE) ──
        (SparseMLE, DenseMLE) => {
            // was: densify for SparseMLE
            let m = val.as_sparse_mle()?;
            let nv = m.num_vars();
            let evals = m.to_evaluations();
            Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(nv, evals)))
        }
        (DenseMLE, SparseMLE) => {
            // was: sparsify for DenseMLE
            let m = val.as_mle()?;
            let nv = m.num_vars();
            let sparse_evals: Vec<(usize, Fr)> = m.to_evaluations().iter()
                .enumerate()
                .filter(|(_, v)| !v.is_zero())
                .map(|(i, v)| (i, *v))
                .collect();
            Ok(Value::SparseMLE(SparseMultilinearExtension::from_evaluations(nv, &sparse_evals)))
        }

        // ── Domain change: UV ↔ MLE ──
        (DenseMLE, DensePoly) => {
            // was: as-uv for DenseMLE
            let m = val.as_mle()?;
            if m.num_vars() != 1 {
                return Err(EvalError::TypeError(format!(
                    "coerce DenseMLE→DensePoly: MLE must have 1 variable, got {}", m.num_vars()
                )));
            }
            let evals = m.to_evaluations();
            let c0 = evals[0];
            let c1 = evals[1] - evals[0];
            Ok(Value::Polynomial(DensePolynomial::from_coefficients_vec(vec![c0, c1])))
        }
        (SparseMLE, SparsePoly) => {
            // was: as-uv for SparseMLE
            let m = val.as_sparse_mle()?;
            if m.num_vars() != 1 {
                return Err(EvalError::TypeError(format!(
                    "coerce SparseMLE→SparsePoly: MLE must have 1 variable, got {}", m.num_vars()
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
        (DensePoly, DenseMLE) => {
            // was: as-mle for DensePolynomial
            let p = val.as_polynomial()?;
            let v0 = p.evaluate(&Fr::from(0u64));
            let v1 = p.evaluate(&Fr::from(1u64));
            Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(1, vec![v0, v1])))
        }
        (SparsePoly, SparseMLE) => {
            // was: as-mle for SparseUVPolynomial
            let p = val.as_sparse_uv_poly()?;
            let v0 = Polynomial::evaluate(&p, &Fr::from(0u64));
            let v1 = Polynomial::evaluate(&p, &Fr::from(1u64));
            let mut evals = Vec::new();
            if !v0.is_zero() { evals.push((0, v0)); }
            if !v1.is_zero() { evals.push((1, v1)); }
            Ok(Value::SparseMLE(SparseMultilinearExtension::from_evaluations(1, &evals)))
        }

        // ── ArrayOf(Field) → DensePoly (coefficients array) ──
        (ArrayOf(inner), DensePoly) if **inner == Field => {
            let arr = val.as_array()?;
            let coeffs: Vec<Fr> = arr.into_iter()
                .map(|v| v.as_field())
                .collect::<Result<_, _>>()?;
            Ok(Value::Polynomial(DensePolynomial::from_coefficients_vec(coeffs)))
        }

        // ── ArrayOf(Field) → DenseMLE (evaluations array, infer num_vars) ──
        (ArrayOf(inner), DenseMLE) if **inner == Field => {
            let arr = val.as_array()?;
            let len = arr.len();
            if len == 0 || (len & (len - 1)) != 0 {
                return Err(EvalError::TypeError(format!(
                    "coerce Array→DenseMLE: array length {} must be a power of 2", len
                )));
            }
            let num_vars = (len as f64).log2() as usize;
            let fr_vals: Vec<Fr> = arr.into_iter()
                .map(|v| v.as_field())
                .collect::<Result<_, _>>()?;
            Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(num_vars, fr_vals)))
        }

        // ── Invalid coercion ──
        _ => Err(EvalError::TypeError(format!(
            "coerce: no valid coercion from {:?} to {:?}", src, dst
        ))),
    }
}

/// Strictly-typed add: both operands must already match their declared types.
/// No implicit coercion — cross-type Int↔Field requires explicit coerce.
fn typed_add(ty_a: ArkType, ty_b: ArkType, va: Value, vb: Value) -> Result<Value, EvalError> {
    use ArkType::*;
    match (&ty_a, &ty_b) {
        (Field, Field) => Ok(Value::Field(va.as_field()? + vb.as_field()?)),
        (Int, Int) => Ok(Value::Int(va.as_int()? + vb.as_int()?)),
        (Curve, Curve) => Ok(Value::Curve(va.as_curve()? + vb.as_curve()?)),
        (DensePoly, DensePoly) => {
            let pa = va.as_polynomial()?;
            let pb = vb.as_polynomial()?;
            Ok(Value::Polynomial(&pa + &pb))
        }
        (SparsePoly, SparsePoly) => {
            let pa = va.as_sparse_uv_poly()?;
            let pb = vb.as_sparse_uv_poly()?;
            Ok(Value::SparseUVPoly(&pa + &pb))
        }
        (DenseMLE, DenseMLE) => {
            let ma = va.as_mle()?;
            let mb = vb.as_mle()?;
            if ma.num_vars() != mb.num_vars() {
                return Err(EvalError::TypeError(format!(
                    "add: MLE num_vars mismatch ({} vs {})", ma.num_vars(), mb.num_vars()
                )));
            }
            Ok(Value::MLE(&ma + &mb))
        }
        (MVPoly, MVPoly) => {
            let pa = va.as_mvpoly()?;
            let pb = vb.as_mvpoly()?;
            Ok(Value::MVPoly(&pa + &pb))
        }
        (ArrayOf(_), ArrayOf(_)) => {
            let arr_a = va.as_array()?;
            let arr_b = vb.as_array()?;
            let len = arr_a.len().max(arr_b.len());
            let mut result = Vec::with_capacity(len);
            for i in 0..len {
                let fa = if i < arr_a.len() { arr_a[i].as_field()? } else { Fr::zero() };
                let fb = if i < arr_b.len() { arr_b[i].as_field()? } else { Fr::zero() };
                result.push(Value::Field(fa + fb));
            }
            Ok(Value::Array(result))
        }
        _ => Err(EvalError::TypeError(format!(
            "add: incompatible types {:?} and {:?}", ty_a, ty_b
        ))),
    }
}

/// Strictly-typed neg: operand must match declared type.
fn typed_neg(ty: ArkType, va: Value) -> Result<Value, EvalError> {
    use ArkType::*;
    match ty {
        Field => Ok(Value::Field(-va.as_field()?)),
        Int => Ok(Value::Int(-va.as_int()?)),
        Curve => Ok(Value::Curve(-va.as_curve()?)),
        DensePoly => Ok(Value::Polynomial(-va.as_polynomial()?)),
        SparsePoly => {
            let p = va.as_sparse_uv_poly()?;
            let neg_coeffs: Vec<(usize, Fr)> = p.to_vec().iter()
                .map(|(i, c)| (*i, -(*c)))
                .collect();
            Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(neg_coeffs)))
        }
        DenseMLE => {
            let m = va.as_mle()?;
            let nv = m.num_vars();
            let neg_evals: Vec<Fr> = m.to_evaluations().iter().map(|v| -(*v)).collect();
            Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(nv, neg_evals)))
        }
        MVPoly => {
            let p = va.as_mvpoly()?;
            let nv = p.num_vars();
            let neg_terms: Vec<(Fr, SparseTerm)> = p.terms().iter()
                .map(|(c, t)| (-(*c), t.clone()))
                .collect();
            Ok(Value::MVPoly(MVSparsePolynomial::from_coefficients_vec(nv, neg_terms)))
        }
        _ => Err(EvalError::TypeError(format!("neg: unsupported type {:?}", ty))),
    }
}

/// Strictly-typed mul: handles same-type products and cross-type scalar multiplication.
fn typed_mul(ty_a: ArkType, ty_b: ArkType, va: Value, vb: Value) -> Result<Value, EvalError> {
    use ArkType::*;
    match (&ty_a, &ty_b) {
        // Same-type products
        (Field, Field) => Ok(Value::Field(va.as_field()? * vb.as_field()?)),
        (Int, Int) => Ok(Value::Int(va.as_int()? * vb.as_int()?)),
        (DensePoly, DensePoly) => {
            let pa = va.as_polynomial()?;
            let pb = vb.as_polynomial()?;
            Ok(Value::Polynomial(&pa * &pb))
        }

        // Scalar × T (absorbed from scale)
        (Field, Curve) | (Int, Curve) => {
            let s = va.as_field()?;
            Ok(Value::Curve(vb.as_curve()? * s))
        }
        (Field, DensePoly) | (Int, DensePoly) => {
            let s = va.as_field()?;
            Ok(Value::Polynomial(&vb.as_polynomial()? * s))
        }
        (Field, SparsePoly) | (Int, SparsePoly) => {
            let s = va.as_field()?;
            let p = vb.as_sparse_uv_poly()?;
            let scaled: Vec<(usize, Fr)> = p.to_vec().iter()
                .map(|(i, coeff)| (*i, *coeff * s))
                .collect();
            Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(scaled)))
        }
        (Field, DenseMLE) | (Int, DenseMLE) => {
            let s = va.as_field()?;
            let m = vb.as_mle()?;
            let nv = m.num_vars();
            let scaled_evals: Vec<Fr> = m.to_evaluations().iter().map(|v| *v * s).collect();
            Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(nv, scaled_evals)))
        }
        (Field, MVPoly) | (Int, MVPoly) => {
            let s = va.as_field()?;
            let p = vb.as_mvpoly()?;
            let nv = p.num_vars();
            let scaled_terms: Vec<(Fr, SparseTerm)> = p.terms().iter()
                .map(|(c, t)| (*c * s, t.clone()))
                .collect();
            Ok(Value::MVPoly(MVSparsePolynomial::from_coefficients_vec(nv, scaled_terms)))
        }
        (Field, Int) => Ok(Value::Field(va.as_field()? * int_to_fr(vb.as_int()?))),

        // T × Scalar (commutative)
        (Curve, Field) | (Curve, Int) => {
            let s = vb.as_field()?;
            Ok(Value::Curve(va.as_curve()? * s))
        }
        (DensePoly, Field) | (DensePoly, Int) => {
            let s = vb.as_field()?;
            Ok(Value::Polynomial(&va.as_polynomial()? * s))
        }
        (SparsePoly, Field) | (SparsePoly, Int) => {
            let s = vb.as_field()?;
            let p = va.as_sparse_uv_poly()?;
            let scaled: Vec<(usize, Fr)> = p.to_vec().iter()
                .map(|(i, coeff)| (*i, *coeff * s))
                .collect();
            Ok(Value::SparseUVPoly(SparseUVPolynomial::from_coefficients_vec(scaled)))
        }
        (DenseMLE, Field) | (DenseMLE, Int) => {
            let s = vb.as_field()?;
            let m = va.as_mle()?;
            let nv = m.num_vars();
            let scaled_evals: Vec<Fr> = m.to_evaluations().iter().map(|v| *v * s).collect();
            Ok(Value::MLE(DenseMultilinearExtension::from_evaluations_vec(nv, scaled_evals)))
        }
        (MVPoly, Field) | (MVPoly, Int) => {
            let s = vb.as_field()?;
            let p = va.as_mvpoly()?;
            let nv = p.num_vars();
            let scaled_terms: Vec<(Fr, SparseTerm)> = p.terms().iter()
                .map(|(c, t)| (*c * s, t.clone()))
                .collect();
            Ok(Value::MVPoly(MVSparsePolynomial::from_coefficients_vec(nv, scaled_terms)))
        }
        (Int, Field) => Ok(Value::Field(int_to_fr(va.as_int()?) * vb.as_field()?)),

        // Hadamard (element-wise) product for arrays
        (ArrayOf(inner_a), ArrayOf(inner_b)) => {
            let arr_a = va.as_array()?;
            let arr_b = vb.as_array()?;
            if arr_a.len() != arr_b.len() {
                return Err(EvalError::TypeError(format!(
                    "mul: array length mismatch: {} vs {}", arr_a.len(), arr_b.len()
                )));
            }
            let results: Vec<Value> = arr_a.into_iter().zip(arr_b.into_iter())
                .map(|(a, b)| typed_mul(inner_a.as_ref().clone(), inner_b.as_ref().clone(), a, b))
                .collect::<Result<_, _>>()?;
            Ok(Value::Array(results))
        }

        _ => Err(EvalError::TypeError(format!(
            "mul: incompatible types {:?} and {:?}", ty_a, ty_b
        ))),
    }
}

/// Evaluate poly-specific operations (fix).
fn eval_poly_specific(expr: &RecExpr<ArkLang>, node: &ArkLang, env: &Env) -> Result<Value, EvalError> {
    match node {
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
        ArkLang::Pow([_t, base, exp]) => {
            let base_node = &expr[*base];
            if let ArkLang::Symbol(s) = base_node {
                if let Some(idx) = var_names.iter().position(|v| v == s) {
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
            let v = eval_id(expr, id, env)?;
            let f = v.as_field().map_err(|_| EvalError::TypeError(
                "poly: pow expression that is not (pow T <var> <exp>) must evaluate to a field element".into()
            ))?;
            Ok((f, vec![0; num_vars]))
        }
        ArkLang::Mul([_ta, _tb, a, b]) => {
            let (ca, ea) = interpret_monomial(expr, *a, var_names, num_vars, env)?;
            let (cb, eb) = interpret_monomial(expr, *b, var_names, num_vars, env)?;
            let coeff = ca * cb;
            let exps: Vec<usize> = ea.iter().zip(eb.iter()).map(|(x, y)| x + y).collect();
            Ok((coeff, exps))
        }
        ArkLang::Neg([_t, a]) => {
            let (ca, ea) = interpret_monomial(expr, *a, var_names, num_vars, env)?;
            Ok((-ca, ea))
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

    fn fr(n: u64) -> Fr {
        Fr::from(n)
    }

    fn eval_str(s: &str, env: &Env) -> Result<Value, EvalError> {
        let expr: RecExpr<ArkLang> = s.parse().expect("parse failed");
        eval(&expr, env)
    }

    // ── Field Arithmetic Tests ──

    #[test]
    fn test_field_add() {
        let v = eval_str("(add Int Int 3 7)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(10));
    }

    #[test]
    fn test_field_sub() {
        let v = eval_str("(add Int Int 10 (neg Int 3))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(7));
    }

    #[test]
    fn test_field_mul() {
        let v = eval_str("(mul Int Int 6 7)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn test_field_neg() {
        let v = eval_str("(add Int Int 5 (neg Int 5))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(0));
    }

    #[test]
    fn test_field_inv() {
        let v = eval_str("(mul Field Field 3 (inv Field (coerce Int Field 3)))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(1));
    }

    #[test]
    fn test_field_div() {
        // 42 / 7 = 6: (mul 42 (inv 7))
        let v = eval_str("(mul Field Field 42 (inv Field (coerce Int Field 7)))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(6));
    }

    #[test]
    fn test_field_inv_zero() {
        let r = eval_str("(inv Field (coerce Int Field 0))", &empty_env());
        assert!(matches!(r, Err(EvalError::DivisionByZero)));
    }

    #[test]
    fn test_field_pow() {
        let v = eval_str("(pow Field (coerce Int Field 2) 10)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(1024));
    }

    #[test]
    fn test_field_additive_identity() {
        let v = eval_str("(add Int Int 42 0)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn test_field_multiplicative_identity() {
        let v = eval_str("(mul Int Int 42 1)", &empty_env()).unwrap();
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
        let v = eval_str("(let x 5 (mul Int Int x x))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(25));
    }

    #[test]
    fn test_let_nested() {
        let v = eval_str("(let x 3 (let y 4 (add Int Int (mul Int Int x x) (mul Int Int y y))))", &empty_env())
            .unwrap();
        assert_eq!(v, Value::Int(25));
    }

    // ── Conditional Tests ──

    #[test]
    fn test_if_true() {
        let v = eval_str("(if (eq Int 1 1) 42 0)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn test_if_false() {
        let v = eval_str("(if (eq Int 1 2) 42 0)", &empty_env()).unwrap();
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

        let result = eval_str("(add Curve Curve p q)", &env).unwrap().as_curve().unwrap();
        assert_eq!(result.into_affine(), (p + q).into_affine());
    }

    #[test]
    fn test_curve_neg() {
        let mut rng = StdRng::seed_from_u64(2);
        let p = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("p".into(), Value::Curve(p));

        let result = eval_str("(add Curve Curve p (neg Curve p))", &env).unwrap().as_curve().unwrap();
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

        let result = eval_str("(mul Field Curve s p)", &env).unwrap().as_curve().unwrap();
        assert_eq!(result.into_affine(), (p * s).into_affine());
    }

    #[test]
    fn test_scalar_mul_integer() {
        let mut rng = StdRng::seed_from_u64(4);
        let p = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("p".into(), Value::Curve(p));

        let result = eval_str("(mul Field Curve 3 p)", &env).unwrap().as_curve().unwrap();
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
            "(add Curve Curve (mul Field Curve a p) (mul Field Curve b q))", &env
        ).unwrap().as_curve().unwrap();

        let expected = p * a + q * b;
        assert_eq!(result.into_affine(), expected.into_affine());
    }

    // ── Polynomial Tests ──

    #[test]
    fn test_poly_eval() {
        let v = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 1 2 3)) 5)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(86));
    }

    #[test]
    fn test_poly_eval_constant() {
        let v = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 42)) 999)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn test_poly_add() {
        let v = eval_str("(eval DensePoly (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 2)) (coerce (arrayof Field) DensePoly (array 3 4))) 10)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(64));
    }

    #[test]
    fn test_poly_mul() {
        let v = eval_str("(eval DensePoly (mul DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 1)) (coerce (arrayof Field) DensePoly (array 1 1))) 3)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(16));
    }

    #[test]
    fn test_poly_sub() {
        let v = eval_str("(eval DensePoly (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 2 3)) (neg DensePoly (coerce (arrayof Field) DensePoly (array 1 2)))) 2)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(12));
    }

    #[test]
    fn test_poly_neg() {
        let v = eval_str("(eval DensePoly (add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 1)) (neg DensePoly (coerce (arrayof Field) DensePoly (array 1 1)))) 7)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(0));
    }

    #[test]
    fn test_poly_div() {
        // pdiv now returns a Pair(quotient, remainder)
        let v = eval_str("(eval DensePoly (fst (div DensePoly (coerce (arrayof Field) DensePoly (array 1 3 2)) (coerce (arrayof Field) DensePoly (array 1 1)))) 5)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(11));
    }

    #[test]
    fn test_poly_mod() {
        let v = eval_str("(eval DensePoly (snd (div DensePoly (coerce (arrayof Field) DensePoly (array 1 0 1)) (coerce (arrayof Field) DensePoly (array 1 1)))) 999)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(2));
    }

    #[test]
    fn test_poly_deg() {
        let v = eval_str("(deg DensePoly (coerce (arrayof Field) DensePoly (array 1 2 3)))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(2));
    }

    #[test]
    fn test_poly_mul_scalar() {
        let v = eval_str("(eval DensePoly (mul Field DensePoly 3 (coerce (arrayof Field) DensePoly (array 1 1))) 2)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(9));
    }

    // ── MLE Tests ──

    #[test]
    fn test_mle_construct_and_eval() {
        let v = eval_str("(eval DenseMLE (coerce (arrayof Field) DenseMLE (array 1 2 3 4)) (array 0 0))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(1));

        let v = eval_str("(eval DenseMLE (coerce (arrayof Field) DenseMLE (array 1 2 3 4)) (array 1 0))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(2));
    }

    #[test]
    fn test_mle_nvars() {
        let v = eval_str("(numvars DenseMLE (coerce (arrayof Field) DenseMLE (array 0 1 2 3 4 5 6 7)))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(3));
    }

    #[test]
    fn test_mle_fix_variables() {
        let v = eval_str(
            "(eval DenseMLE (fix (coerce (arrayof Field) DenseMLE (array 1 2 3 4)) (array 1)) (array 0))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v, Value::Int(2));
    }

    #[test]
    fn test_mle_add() {
        let v = eval_str(
            "(eval DenseMLE (add DenseMLE DenseMLE (coerce (arrayof Field) DenseMLE (array 1 0 0 0)) (coerce (arrayof Field) DenseMLE (array 0 0 0 1))) (array 0 0))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v, Value::Int(1));
    }

    // ── Multivariate Polynomial Tests ──

    #[test]
    fn test_mvpoly_construct_and_eval() {
        let v = eval_str(
            "(eval MVPoly (poly (ids x y) 5 (mul Field Field 2 x) (mul Field Field 3 y)) (array 2 7))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v, Value::Int(30));
    }

    #[test]
    fn test_mvpoly_degree() {
        let v = eval_str(
            "(deg MVPoly (poly (ids x y) (mul Field Field (pow Field x 2) y)))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v, Value::Int(3));
    }

    #[test]
    fn test_mvpoly_add() {
        let v = eval_str(
            "(eval MVPoly (add MVPoly MVPoly (poly (ids x y) 1 x) (poly (ids x y) 2 y)) (array 1 1))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v, Value::Int(5));
    }

    // ── Array Tests ──

    #[test]
    fn test_array_create_and_select() {
        let v = eval_str("(get Int (array 10 20 30) 1)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(20));
    }

    #[test]
    fn test_array_len() {
        let v = eval_str("(length (array 1 2 3 4 5))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(5));
    }

    #[test]
    fn test_array_index_out_of_bounds() {
        let r = eval_str("(get Int (array 1 2) 5)", &empty_env());
        assert!(matches!(r, Err(EvalError::IndexOutOfBounds { .. })));
    }

    #[test]
    fn test_store_basic() {
        let v = eval_str("(get Int (set Int (array 1 2 3) 1 99) 1)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(99));
    }

    #[test]
    fn test_store_preserves_other() {
        let v = eval_str("(get Int (set Int (array 1 2 3) 1 99) 0)", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(1));
    }

    #[test]
    fn test_store_out_of_bounds() {
        let r = eval_str("(set Int (array 1 2 3) 5 99)", &empty_env());
        assert!(matches!(r, Err(EvalError::IndexOutOfBounds { .. })));
    }

    #[test]
    fn test_alen_after_store() {
        let v = eval_str("(length (set Int (array 1 2 3) 0 99))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(3));
    }

    #[test]
    fn test_store_type_mismatch() {
        let mut rng = StdRng::seed_from_u64(100);
        let p = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("p".into(), Value::Curve(p));
        let r = eval_str("(set Int (array 1 2 3) 0 p)", &env);
        assert!(matches!(r, Err(EvalError::TypeMismatch { .. })));
    }

    // ── Complex Expression Tests ──

    #[test]
    fn test_nested_field_expression() {
        // (3 + 4) * (5 - 2) = 7 * 3 = 21
        let v = eval_str("(mul Int Int (add Int Int 3 4) (add Int Int 5 (neg Int 2)))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(21));
    }

    #[test]
    fn test_horner_form() {
        let mut env = empty_env();
        env.insert("x".into(), Value::Int(5));
        let v = eval_str("(add Int Int 1 (mul Int Int x (add Int Int 2 (mul Int Int x 3))))", &env).unwrap();
        assert_eq!(v, Value::Int(86));
    }

    #[test]
    fn test_polynomial_vs_horner_equivalence() {
        let mut env = empty_env();
        env.insert("x".into(), Value::Int(7));

        let poly_result = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 5 3 2 1)) x)", &env)
            .unwrap()
            .as_field()
            .unwrap();
        let horner_result = eval_str(
            "(add Field Field 5 (mul Field Field x (add Field Field 3 (mul Field Field x (add Field Field 2 (mul Field Field x 1))))))",
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
        let v = eval_str("(eval SparsePoly (poly (ids x) 5 (mul Field Field 3 (pow Field x 2))) 2)", &empty_env()).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(17u64));
    }

    #[test]
    fn test_sparse_uv_single_term() {
        let v = eval_str("(eval SparsePoly (poly (ids x) (mul Field Field 7 (pow Field x 3))) 2)", &empty_env()).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(56u64));
    }

    // ── Sparse MLE Tests ──

    #[test]
    fn test_sparse_mle_eval() {
        let v = eval_str(
            "(eval SparseMLE (coerce DenseMLE SparseMLE (coerce (arrayof Field) DenseMLE (array 10 0 0 20))) (array 0 0))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(10u64));
    }

    #[test]
    fn test_sparse_mle_eval_at_one_one() {
        let v = eval_str(
            "(eval SparseMLE (coerce DenseMLE SparseMLE (coerce (arrayof Field) DenseMLE (array 10 0 0 20))) (array 1 1))",
            &empty_env(),
        ).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(20u64));
    }

    // ── Sigma/Pi Tests ──

    #[test]
    fn test_sigma_sum() {
        let v = eval_str("(Σ i 0 3 (get Int (array 10 20 30) i))", &empty_env()).unwrap();
        assert_eq!(v, Value::Int(60));
    }

    #[test]
    fn test_sigma_mul_scalar() {
        let mut rng = StdRng::seed_from_u64(50);
        let p0 = G1Projective::rand(&mut rng);
        let p1 = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("P0".into(), Value::Curve(p0));
        env.insert("P1".into(), Value::Curve(p1));

        let result = eval_str(
            "(Σ i 0 2 (mul Field Curve (get Int (array 3 5) i) (get Curve (array P0 P1) i)))",
            &env,
        ).unwrap().as_curve().unwrap();

        let expected = p0 * Fr::from(3u64) + p1 * Fr::from(5u64);
        assert_eq!(result.into_affine(), expected.into_affine());
    }

    #[test]
    fn test_pi_product() {
        let v = eval_str("(Π i 0 3 (get Int (array 2 3 5) i))", &empty_env()).unwrap();
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
        let v = eval_str("(eval DensePoly (coerce SparsePoly DensePoly (poly (ids x) 5 (mul Field Field 3 (pow Field x 2)))) 2)", &empty_env()).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(17u64));
    }

    #[test]
    fn test_sparsify_dense_uv() {
        // Create dense poly [5, 0, 3] (5 + 3x^2), sparsify, evaluate
        let v = eval_str("(eval SparsePoly (coerce DensePoly SparsePoly (coerce (arrayof Field) DensePoly (array 5 0 3))) 2)", &empty_env()).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(17u64));
    }

    #[test]
    fn test_as_uv_mle() {
        // 1-var MLE with evals [3, 7]: linear poly f(x) = 3 + 4x
        // Evaluate at x=2: 3 + 8 = 11
        let v = eval_str("(eval DensePoly (coerce DenseMLE DensePoly (coerce (arrayof Field) DenseMLE (array 3 7))) 2)", &empty_env()).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(11u64));
    }

    #[test]
    fn test_as_mle_uv() {
        // UV poly [3, 4] (3 + 4x) → MLE with 1 var
        // Eval at (0) → 3, eval at (1) → 7
        let v0 = eval_str("(eval DenseMLE (coerce DensePoly DenseMLE (coerce (arrayof Field) DensePoly (array 3 4))) (array 0))", &empty_env()).unwrap();
        assert_eq!(v0.as_field().unwrap(), Fr::from(3u64));
        let v1 = eval_str("(eval DenseMLE (coerce DensePoly DenseMLE (coerce (arrayof Field) DensePoly (array 3 4))) (array 1))", &empty_env()).unwrap();
        assert_eq!(v1.as_field().unwrap(), Fr::from(7u64));
    }

    // ── Staging Pipeline Tests ──

    #[test]
    fn test_specialize_bound() {
        // Build: (let N (bound 2 100) (Σ i 0 N (get Int (array 10 20 30) i)))
        // Specialize N=3
        // Should evaluate to 10+20+30 = 60
        let expr: RecExpr<ArkLang> =
            "(let N (bound 2 100) (Σ i 0 N (get Int (array 10 20 30) i)))".parse().unwrap();
        let specialized = specialize(&expr, "N".into(), 3);
        let result = eval(&specialized, &empty_env()).unwrap();
        assert_eq!(result.as_field().unwrap(), Fr::from(60u64));
    }

    #[test]
    fn test_specialize_msm_pattern() {
        // Parametric MSM: (let N (bound 1 10) (Σ i 0 N (mul Field Curve (get s i) (get P i))))
        // Specialize N=2 with concrete scalars and points
        let mut rng = StdRng::seed_from_u64(42);
        let p0 = G1Projective::rand(&mut rng);
        let p1 = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert("s".into(), Value::Array(vec![Value::Int(3), Value::Int(5)]));
        env.insert("P".into(), Value::Array(vec![Value::Curve(p0), Value::Curve(p1)]));

        let expr: RecExpr<ArkLang> =
            "(let N (bound 1 10) (Σ i 0 N (mul Field Curve (get Int s i) (get Curve P i))))".parse().unwrap();
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
        let v = eval_str("(fft DensePoly 4 (coerce (arrayof Field) DensePoly (array 5)))", &empty_env()).unwrap();
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
        let evals = eval_str("(fft DensePoly 4 (coerce (arrayof Field) DensePoly (array 1 2)))", &env).unwrap().as_array().unwrap();
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
        let original = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 3 5 7)) 42)", &env).unwrap().as_field().unwrap();
        let recovered = eval_str("(eval DensePoly (ifft Array 4 (fft DensePoly 4 (coerce (arrayof Field) DensePoly (array 3 5 7)))) 42)", &env).unwrap().as_field().unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn test_fft_from_array() {
        // FFT should accept Array[Field] as raw coefficients
        let env = empty_env();
        let from_poly = eval_str("(fft DensePoly 4 (coerce (arrayof Field) DensePoly (array 1 2 3)))", &env).unwrap();
        let from_arr = eval_str("(fft Array 4 (array 1 2 3))", &env).unwrap();
        assert_eq!(from_poly, from_arr);
    }

    #[test]
    fn test_fft_from_sparse() {
        // FFT should accept SparseUVPoly
        let env = empty_env();
        let from_dense = eval_str("(fft DensePoly 4 (coerce (arrayof Field) DensePoly (array 5 0 3)))", &env).unwrap();
        let from_sparse = eval_str("(fft SparsePoly 4 (poly (ids x) 5 (mul Field Field 3 (pow Field x 2))))", &env).unwrap();
        assert_eq!(from_dense, from_sparse);
    }

    #[test]
    fn test_fft_eval_matches_point_eval() {
        // FFT evaluations should match point-by-point eval at domain elements
        let env = empty_env();
        let evals = eval_str("(fft DensePoly 8 (coerce (arrayof Field) DensePoly (array 1 2 3 4)))", &env).unwrap().as_array().unwrap();
        let domain_pts = eval_str("(domain 8)", &env).unwrap().as_array().unwrap();
        for i in 0..8 {
            let pt = domain_pts[i].as_field().unwrap();
            let mut env2 = empty_env();
            env2.insert("x".into(), Value::Field(pt));
            let point_eval = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 1 2 3 4)) x)", &env2).unwrap().as_field().unwrap();
            assert_eq!(evals[i].as_field().unwrap(), point_eval);
        }
    }

    // ── Symbolic Polynomial Constructor Tests ──

    #[test]
    fn test_poly_univariate_basic() {
        // (poly (ids x) (mul Field Field 3 (pow Field x 2)) (mul Field Field 5 x) 7) = 3x² + 5x + 7
        let env = empty_env();
        let v = eval_str("(eval SparsePoly (poly (ids x) (mul Field Field 3 (pow Field x 2)) (mul Field Field 5 x) 7) 2)", &env).unwrap();
        // 3*4 + 5*2 + 7 = 12 + 10 + 7 = 29
        assert_eq!(v.as_field().unwrap(), Fr::from(29u64));
    }

    #[test]
    fn test_poly_univariate_matches_suv() {
        // (poly (ids x) (mul Field Field 3 (pow Field x 2)) (mul Field Field 5 x) 7) should match (poly:suv 0 7 1 5 2 3)
        let env = empty_env();
        let from_sym = eval_str("(eval SparsePoly (poly (ids x) (mul Field Field 3 (pow Field x 2)) (mul Field Field 5 x) 7) 10)", &env).unwrap();
        let from_suv = eval_str("(eval SparsePoly (poly (ids x) 7 (mul Field Field 5 x) (mul Field Field 3 (pow Field x 2))) 10)", &env).unwrap();
        assert_eq!(from_sym.as_field().unwrap(), from_suv.as_field().unwrap());
    }

    #[test]
    fn test_poly_bare_variable() {
        // (poly (ids x) x) = x
        let env = empty_env();
        let v = eval_str("(eval SparsePoly (poly (ids x) x) 42)", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(42u64));
    }

    #[test]
    fn test_poly_constant() {
        // (poly (ids x) 5) = constant polynomial 5
        let env = empty_env();
        let v = eval_str("(eval SparsePoly (poly (ids x) 5) 99)", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(5u64));
    }

    #[test]
    fn test_poly_negative_coeff() {
        // (poly (ids x) (neg Field (pow Field x 2)) x) = -x² + x
        let env = empty_env();
        let v = eval_str("(eval SparsePoly (poly (ids x) (neg Field (pow Field x 2)) x) 3)", &env).unwrap();
        // -9 + 3 = -6 in the field
        let expected = -Fr::from(9u64) + Fr::from(3u64);
        assert_eq!(v.as_field().unwrap(), expected);
    }

    #[test]
    fn test_poly_multivariate() {
        // (poly (ids x y) (pow Field x 2) (pow Field y 3) 4) = x² + y³ + 4
        let env = empty_env();
        let v = eval_str(
            "(eval MVPoly (poly (ids x y) (pow Field x 2) (pow Field y 3) 4) (array 3 2))",
            &env,
        ).unwrap();
        // 9 + 8 + 4 = 21
        assert_eq!(v.as_field().unwrap(), Fr::from(21u64));
    }

    #[test]
    fn test_poly_multivariate_cross_term() {
        // (poly (ids x y) (mul Field Field 2 (mul Field Field x y))) = 2xy
        let env = empty_env();
        let v = eval_str(
            "(eval MVPoly (poly (ids x y) (mul Field Field 2 (mul Field Field x y))) (array 3 5))",
            &env,
        ).unwrap();
        // 2*3*5 = 30
        assert_eq!(v.as_field().unwrap(), Fr::from(30u64));
    }

    #[test]
    fn test_poly_env_exponent() {
        // (poly (ids x) (pow Field x n)) where n comes from environment
        let mut env = empty_env();
        env.insert("n".into(), Value::Int(3));
        let v = eval_str("(eval SparsePoly (poly (ids x) (pow Field x n)) 2)", &env).unwrap();
        // 2³ = 8
        assert_eq!(v.as_field().unwrap(), Fr::from(8u64));
    }

    #[test]
    fn test_poly_env_coefficient() {
        // (poly (ids x) (mul Field Field c (pow Field x 2))) where c comes from environment
        let mut env = empty_env();
        env.insert("c".into(), Value::Field(Fr::from(7u64)));
        let v = eval_str("(eval SparsePoly (poly (ids x) (mul Field Field c (pow Field x 2))) 3)", &env).unwrap();
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
        let q = eval_str("(eval DensePoly (fst (div DensePoly (coerce (arrayof Field) DensePoly (array 1 3 2)) (coerce (arrayof Field) DensePoly (array 1 1)))) 5)", &env).unwrap();
        assert_eq!(q.as_field().unwrap(), Fr::from(11u64));
        let r = eval_str("(eval DensePoly (snd (div DensePoly (coerce (arrayof Field) DensePoly (array 1 3 2)) (coerce (arrayof Field) DensePoly (array 1 1)))) 5)", &env).unwrap();
        assert_eq!(r.as_field().unwrap(), Fr::from(0u64));
    }

    #[test]
    fn test_pdiv_division_identity() {
        // a = q*b + r: (x² + 1) / (x + 1) → q = x - 1, r = 2
        // Verify: q*b + r = a at x = 5
        let env = empty_env();
        let a_val = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 1 0 1)) 5)", &env).unwrap().as_field().unwrap();
        let q_val = eval_str("(eval DensePoly (fst (div DensePoly (coerce (arrayof Field) DensePoly (array 1 0 1)) (coerce (arrayof Field) DensePoly (array 1 1)))) 5)", &env).unwrap().as_field().unwrap();
        let b_val = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 1 1)) 5)", &env).unwrap().as_field().unwrap();
        let r_val = eval_str("(eval DensePoly (snd (div DensePoly (coerce (arrayof Field) DensePoly (array 1 0 1)) (coerce (arrayof Field) DensePoly (array 1 1)))) 5)", &env).unwrap().as_field().unwrap();
        assert_eq!(a_val, q_val * b_val + r_val);
    }

    // ── Array Addition Tests ──

    #[test]
    fn test_aadd_basic() {
        let env = empty_env();
        let v = eval_str("(add (arrayof Field) (arrayof Field) (array 1 2 3) (array 4 5 6))", &env).unwrap().as_array().unwrap();
        assert_eq!(v.len(), 3);
        assert_eq!(v[0].as_field().unwrap(), Fr::from(5u64));
        assert_eq!(v[1].as_field().unwrap(), Fr::from(7u64));
        assert_eq!(v[2].as_field().unwrap(), Fr::from(9u64));
    }

    #[test]
    fn test_aadd_different_lengths() {
        let env = empty_env();
        let v = eval_str("(add (arrayof Field) (arrayof Field) (array 1 2) (array 10 20 30))", &env).unwrap().as_array().unwrap();
        assert_eq!(v.len(), 3);
        assert_eq!(v[0].as_field().unwrap(), Fr::from(11u64));
        assert_eq!(v[1].as_field().unwrap(), Fr::from(22u64));
        assert_eq!(v[2].as_field().unwrap(), Fr::from(30u64));
    }

    #[test]
    fn test_aadd_empty() {
        let env = empty_env();
        let v = eval_str("(add (arrayof Field) (arrayof Field) (array) (array 1 2))", &env).unwrap().as_array().unwrap();
        assert_eq!(v.len(), 2);
        assert_eq!(v[0].as_field().unwrap(), Fr::from(1u64));
    }

    // ═══════════════════════════════════════════════
    // Wave 0: Type tags, coerce, and helpers
    // ═══════════════════════════════════════════════

    #[test]
    fn test_type_tag_not_evaluable() {
        let env = empty_env();
        assert!(eval_str("Field", &env).is_err());
        assert!(eval_str("Int", &env).is_err());
        assert!(eval_str("DensePoly", &env).is_err());
    }

    #[test]
    fn test_coerce_int_to_field() {
        let env = empty_env();
        let v = eval_str("(coerce Int Field 42)", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(42u64));
    }

    #[test]
    fn test_coerce_int_to_field_negative() {
        let env = empty_env();
        let v = eval_str("(coerce Int Field -3)", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), -Fr::from(3u64));
    }

    #[test]
    fn test_coerce_identity() {
        let env = empty_env();
        let v = eval_str("(coerce Field Field (add Field Field 3 7))", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(10u64));
    }

    #[test]
    fn test_coerce_field_to_dense_poly() {
        let env = empty_env();
        let v = eval_str("(coerce Field DensePoly (add Field Field 1 2))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.evaluate(&Fr::from(0u64)), Fr::from(3u64));
        assert_eq!(p.evaluate(&Fr::from(99u64)), Fr::from(3u64)); // constant poly
    }

    #[test]
    fn test_coerce_field_to_sparse_poly() {
        let env = empty_env();
        let v = eval_str("(coerce Field SparsePoly (add Field Field 2 3))", &env).unwrap();
        let p = v.as_sparse_uv_poly().unwrap();
        assert_eq!(Polynomial::evaluate(&p, &Fr::from(0u64)), Fr::from(5u64));
    }

    #[test]
    fn test_coerce_field_to_dense_mle() {
        let env = empty_env();
        let v = eval_str("(coerce Field DenseMLE (add Field Field 1 1))", &env).unwrap();
        let m = v.as_mle().unwrap();
        assert_eq!(m.num_vars(), 1);
        // constant MLE: evaluates to 2 everywhere
        assert_eq!(m.evaluate(&vec![Fr::from(0u64)]), Fr::from(2u64));
        assert_eq!(m.evaluate(&vec![Fr::from(1u64)]), Fr::from(2u64));
    }

    #[test]
    fn test_coerce_field_to_sparse_mle() {
        let env = empty_env();
        let v = eval_str("(coerce Field SparseMLE (add Field Field 3 4))", &env).unwrap();
        let m = v.as_sparse_mle().unwrap();
        assert_eq!(m.num_vars(), 1);
        assert_eq!(m.evaluate(&vec![Fr::from(0u64)]), Fr::from(7u64));
    }

    #[test]
    fn test_coerce_field_to_mvpoly() {
        let env = empty_env();
        let v = eval_str("(coerce Field MVPoly (add Field Field 5 6))", &env).unwrap();
        let p = v.as_mvpoly().unwrap();
        assert_eq!(p.evaluate(&vec![Fr::from(99u64)]), Fr::from(11u64)); // constant
    }

    #[test]
    fn test_coerce_int_to_dense_poly() {
        let env = empty_env();
        let v = eval_str("(coerce Int DensePoly 7)", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.evaluate(&Fr::from(42u64)), Fr::from(7u64)); // constant poly
    }

    #[test]
    fn test_coerce_int_to_sparse_poly() {
        let env = empty_env();
        let v = eval_str("(coerce Int SparsePoly 5)", &env).unwrap();
        let p = v.as_sparse_uv_poly().unwrap();
        assert_eq!(Polynomial::evaluate(&p, &Fr::from(0u64)), Fr::from(5u64));
    }

    #[test]
    fn test_coerce_int_to_dense_mle() {
        let env = empty_env();
        let v = eval_str("(coerce Int DenseMLE 9)", &env).unwrap();
        let m = v.as_mle().unwrap();
        assert_eq!(m.evaluate(&vec![Fr::from(0u64)]), Fr::from(9u64));
    }

    #[test]
    fn test_coerce_int_to_sparse_mle() {
        let env = empty_env();
        let v = eval_str("(coerce Int SparseMLE 4)", &env).unwrap();
        let m = v.as_sparse_mle().unwrap();
        assert_eq!(m.evaluate(&vec![Fr::from(1u64)]), Fr::from(4u64));
    }

    #[test]
    fn test_coerce_int_to_mvpoly() {
        let env = empty_env();
        let v = eval_str("(coerce Int MVPoly 3)", &env).unwrap();
        let p = v.as_mvpoly().unwrap();
        assert_eq!(p.evaluate(&vec![Fr::from(0u64)]), Fr::from(3u64));
    }

    #[test]
    fn test_coerce_sparse_to_dense_poly() {
        let env = empty_env();
        // sparse poly 5 + 3x^2
        let v = eval_str("(coerce SparsePoly DensePoly (poly (ids x) 5 (mul Field Field 3 (pow Field x 2))))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.evaluate(&Fr::from(2u64)), Fr::from(17u64)); // 5 + 3*4
    }

    #[test]
    fn test_coerce_dense_to_sparse_poly() {
        let env = empty_env();
        let v = eval_str("(coerce DensePoly SparsePoly (coerce (arrayof Field) DensePoly (array 5 0 3)))", &env).unwrap();
        let p = v.as_sparse_uv_poly().unwrap();
        assert_eq!(Polynomial::evaluate(&p, &Fr::from(2u64)), Fr::from(17u64)); // 5 + 3*4
    }

    #[test]
    fn test_coerce_dense_mle_to_dense_poly() {
        let env = empty_env();
        // 1-var MLE with evals [3, 7] → linear poly c0=3, c1=4 → 3+4x
        let v = eval_str("(coerce DenseMLE DensePoly (coerce (arrayof Field) DenseMLE (array 3 7)))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.evaluate(&Fr::from(0u64)), Fr::from(3u64));
        assert_eq!(p.evaluate(&Fr::from(1u64)), Fr::from(7u64));
    }

    #[test]
    fn test_coerce_dense_poly_to_dense_mle() {
        let env = empty_env();
        let v = eval_str("(coerce DensePoly DenseMLE (coerce (arrayof Field) DensePoly (array 3 4)))", &env).unwrap();
        let m = v.as_mle().unwrap();
        assert_eq!(m.evaluate(&vec![Fr::from(0u64)]), Fr::from(3u64));
        assert_eq!(m.evaluate(&vec![Fr::from(1u64)]), Fr::from(7u64));
    }

    #[test]
    fn test_coerce_sparse_mle_to_dense_mle() {
        let env = empty_env();
        // 2-var sparse MLE: index 0→3, index 3→7
        let v = eval_str("(coerce SparseMLE DenseMLE (coerce DenseMLE SparseMLE (coerce (arrayof Field) DenseMLE (array 3 0 0 7))))", &env).unwrap();
        let m = v.as_mle().unwrap();
        assert_eq!(m.num_vars(), 2);
    }

    #[test]
    fn test_coerce_dense_mle_to_sparse_mle() {
        let env = empty_env();
        let v = eval_str("(coerce DenseMLE SparseMLE (coerce (arrayof Field) DenseMLE (array 0 5)))", &env).unwrap();
        let m = v.as_sparse_mle().unwrap();
        assert_eq!(m.num_vars(), 1);
        assert_eq!(m.evaluate(&vec![Fr::from(1u64)]), Fr::from(5u64));
    }

    #[test]
    fn test_coerce_sparse_mle_to_sparse_poly() {
        let env = empty_env();
        // 1-var sparse MLE: index 0→3, index 1→7 → linear poly 3+4x
        let v = eval_str("(coerce SparseMLE SparsePoly (coerce DenseMLE SparseMLE (coerce (arrayof Field) DenseMLE (array 3 7))))", &env).unwrap();
        let p = v.as_sparse_uv_poly().unwrap();
        assert_eq!(Polynomial::evaluate(&p, &Fr::from(0u64)), Fr::from(3u64));
        assert_eq!(Polynomial::evaluate(&p, &Fr::from(1u64)), Fr::from(7u64));
    }

    #[test]
    fn test_coerce_sparse_poly_to_sparse_mle() {
        let env = empty_env();
        let v = eval_str("(coerce SparsePoly SparseMLE (poly (ids x) 3 (mul Field Field 4 x)))", &env).unwrap();
        let m = v.as_sparse_mle().unwrap();
        assert_eq!(m.num_vars(), 1);
        assert_eq!(m.evaluate(&vec![Fr::from(0u64)]), Fr::from(3u64));
        assert_eq!(m.evaluate(&vec![Fr::from(1u64)]), Fr::from(7u64));
    }

    #[test]
    fn test_coerce_invalid_curve_to_field() {
        let env = empty_env();
        assert!(eval_str("(coerce Curve Field 5)", &env).is_err());
    }

    #[test]
    fn test_coerce_int_as_field_to_dense() {
        let env = empty_env();
        // Int(5) with src tag Field succeeds (Int auto-coerces to Field)
        let v = eval_str("(coerce Field DensePoly 5)", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.evaluate(&Fr::from(99u64)), Fr::from(5u64));
    }

    #[test]
    fn test_coerce_chained() {
        let env = empty_env();
        // Int → Field → DensePoly via two coerces
        let v = eval_str("(coerce Field DensePoly (coerce Int Field 3))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.evaluate(&Fr::from(99u64)), Fr::from(3u64));
    }

    #[test]
    fn test_validate_type_helper() {
        let v = Value::Field(Fr::from(42u64));
        assert!(validate_type(&v, &ArkType::Field).is_ok());
        assert!(validate_type(&v, &ArkType::Int).is_err());
        assert!(validate_type(&v, &ArkType::Curve).is_err());

        let vi = Value::Int(7);
        assert!(validate_type(&vi, &ArkType::Int).is_ok());
        assert!(validate_type(&vi, &ArkType::Field).is_ok()); // Int auto-coerces to Field
    }

    // ═══════════════════════════════════════════════
    // Wave 1: Typed add (add)
    // ═══════════════════════════════════════════════

    #[test]
    fn test_add_field_field() {
        let env = empty_env();
        let v = eval_str("(add Field Field (coerce Int Field 3) (coerce Int Field 7))", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(10u64));
    }

    #[test]
    fn test_add_int_int() {
        let env = empty_env();
        let v = eval_str("(add Int Int 3 7)", &env).unwrap();
        assert_eq!(v, Value::Int(10));
    }

    #[test]
    fn test_add_curve_curve() {
        use ark_ec::CurveGroup;
        use ark_bls12_381::G1Projective;
        use ark_std::UniformRand;
        let mut rng = ark_std::test_rng();
        let p = G1Projective::rand(&mut rng);
        let q = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert(Symbol::from("P"), Value::Curve(p));
        env.insert(Symbol::from("Q"), Value::Curve(q));
        let v = eval_str("(add Curve Curve P Q)", &env).unwrap();
        assert_eq!(v.as_curve().unwrap().into_affine(), (p + q).into_affine());
    }

    #[test]
    fn test_add_dense_poly() {
        let env = empty_env();
        // (1 + 2x) + (3 + 4x) = (4 + 6x)
        let v = eval_str("(add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 2)) (coerce (arrayof Field) DensePoly (array 3 4)))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.evaluate(&Fr::from(0u64)), Fr::from(4u64));
        assert_eq!(p.evaluate(&Fr::from(1u64)), Fr::from(10u64));
    }

    #[test]
    fn test_add_sparse_poly() {
        let env = empty_env();
        let v = eval_str("(add SparsePoly SparsePoly (poly (ids x) 5) (poly (ids x) 3))", &env).unwrap();
        let p = v.as_sparse_uv_poly().unwrap();
        assert_eq!(Polynomial::evaluate(&p, &Fr::from(0u64)), Fr::from(8u64));
    }

    #[test]
    fn test_add_dense_mle() {
        let env = empty_env();
        // 1-var MLEs: [1,3] + [2,4] = [3,7]
        let v = eval_str("(add DenseMLE DenseMLE (coerce (arrayof Field) DenseMLE (array 1 3)) (coerce (arrayof Field) DenseMLE (array 2 4)))", &env).unwrap();
        let m = v.as_mle().unwrap();
        assert_eq!(m.evaluate(&vec![Fr::from(0u64)]), Fr::from(3u64));
        assert_eq!(m.evaluate(&vec![Fr::from(1u64)]), Fr::from(7u64));
    }

    #[test]
    fn test_add_int_as_field() {
        let env = empty_env();
        // Int values auto-coerce to Field when type tag is Field
        let result = eval_str("(add Field Field 3 7)", &env).unwrap();
        assert_eq!(result.as_field().unwrap(), Fr::from(10u64));
    }

    #[test]
    fn test_add_incompatible_types() {
        let env = empty_env();
        // Can't add Field + Curve
        let result = eval_str("(add Field Curve (coerce Int Field 3) (coerce Int Field 7))", &env);
        assert!(result.is_err());
    }

    #[test]
    fn test_add_with_coerced_polys() {
        let env = empty_env();
        // Add a polynomial + a coerced constant
        let v = eval_str("(add DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 2)) (coerce Field DensePoly (coerce Int Field 5)))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        // (1 + 2x) + 5 = (6 + 2x)
        assert_eq!(p.evaluate(&Fr::from(0u64)), Fr::from(6u64));
        assert_eq!(p.evaluate(&Fr::from(1u64)), Fr::from(8u64));
    }

    // ═══════════════════════════════════════════════
    // Wave 2: Typed neg, mul, inv, pow
    // ═══════════════════════════════════════════════

    #[test]
    fn test_neg_field() {
        let env = empty_env();
        let v = eval_str("(neg Field (coerce Int Field 5))", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), -Fr::from(5u64));
    }

    #[test]
    fn test_neg_dense_poly() {
        let env = empty_env();
        let v = eval_str("(neg DensePoly (coerce (arrayof Field) DensePoly (array 1 2)))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.evaluate(&Fr::from(0u64)), -Fr::from(1u64));
        assert_eq!(p.evaluate(&Fr::from(1u64)), -Fr::from(3u64));
    }

    #[test]
    fn test_neg_int_as_field() {
        let env = empty_env();
        // Int auto-coerces to Field when type tag is Field
        let v = eval_str("(neg Field 5)", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), -Fr::from(5u64));
    }

    #[test]
    fn test_mul_field_field() {
        let env = empty_env();
        let v = eval_str("(mul Field Field (coerce Int Field 3) (coerce Int Field 7))", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(21u64));
    }

    #[test]
    fn test_mul_dense_poly() {
        let env = empty_env();
        let v = eval_str("(mul DensePoly DensePoly (coerce (arrayof Field) DensePoly (array 1 1)) (coerce (arrayof Field) DensePoly (array 1 1)))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.evaluate(&Fr::from(2u64)), Fr::from(9u64));
    }

    #[test]
    fn test_mul_incompatible() {
        let env = empty_env();
        assert!(eval_str("(mul Field Curve (coerce Int Field 3) (coerce Int Field 7))", &env).is_err());
    }

    #[test]
    fn test_inv_field() {
        let env = empty_env();
        let v = eval_str("(inv Field (coerce Int Field 2))", &env).unwrap();
        let inv2 = v.as_field().unwrap();
        assert_eq!(inv2 * Fr::from(2u64), Fr::from(1u64));
    }

    #[test]
    fn test_inv_zero() {
        let env = empty_env();
        assert!(eval_str("(inv Field (coerce Int Field 0))", &env).is_err());
    }

    #[test]
    fn test_inv_non_field() {
        let env = empty_env();
        assert!(eval_str("(inv DensePoly (coerce (arrayof Field) DensePoly (array 1 2)))", &env).is_err());
    }

    #[test]
    fn test_mul_scalar_curve() {
        use ark_ec::CurveGroup;
        use ark_bls12_381::G1Projective;
        use ark_std::UniformRand;
        let mut rng = ark_std::test_rng();
        let p = G1Projective::rand(&mut rng);
        let mut env = empty_env();
        env.insert(Symbol::from("P"), Value::Curve(p));
        env.insert(Symbol::from("c"), Value::Field(Fr::from(3u64)));
        let v = eval_str("(mul Field Curve c P)", &env).unwrap();
        assert_eq!(v.as_curve().unwrap().into_affine(), (p * Fr::from(3u64)).into_affine());
    }

    #[test]
    fn test_mul_scalar_dense_poly() {
        let env = empty_env();
        let v = eval_str("(mul Field DensePoly (coerce Int Field 3) (coerce (arrayof Field) DensePoly (array 1 2)))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.evaluate(&Fr::from(1u64)), Fr::from(9u64));
    }

    #[test]
    fn test_mul_int_scalar_coerced() {
        let env = empty_env();
        // Int scalar 3 is auto-coerced to Field for mul
        let v = eval_str("(mul Field Field 3 (coerce Int Field 5))", &env).unwrap();
        assert_eq!(v, Value::Field(fr(15)));
    }

    #[test]
    fn test_pow_field() {
        let env = empty_env();
        let v = eval_str("(pow Field (coerce Int Field 3) 4)", &env).unwrap();
        assert_eq!(v.as_field().unwrap(), Fr::from(81u64));
    }

    #[test]
    fn test_pow_negative_exp() {
        let env = empty_env();
        let v = eval_str("(pow Field (coerce Int Field 2) -1)", &env).unwrap();
        let result = v.as_field().unwrap();
        assert_eq!(result * Fr::from(2u64), Fr::from(1u64));
    }

    #[test]
    fn test_pow_non_field() {
        let env = empty_env();
        assert!(eval_str("(pow DensePoly (coerce (arrayof Field) DensePoly (array 1 2)) 3)", &env).is_err());
    }

    // ═══════════════════════════════════════════════
    // Wave 3: Typed query/poly/array/comparison ops
    // ═══════════════════════════════════════════════

    // ── Eval ──
    #[test]
    fn test_eval_dense_poly() {
        let env = empty_env();
        // p(x) = 1 + 2x, evaluate at x=3 → 1 + 6 = 7
        let v = eval_str("(eval DensePoly (coerce (arrayof Field) DensePoly (array 1 2)) (coerce Int Field 3))", &env).unwrap();
        assert_eq!(v, Value::Field(fr(7)));
    }

    #[test]
    fn test_eval_sparse_poly() {
        let env = empty_env();
        // p(x) = 5x^2, evaluate at x=2 → 20
        let v = eval_str("(eval SparsePoly (poly (ids x) (mul Field Field 5 (pow Field x 2))) (coerce Int Field 2))", &env).unwrap();
        assert_eq!(v, Value::Field(fr(20)));
    }

    #[test]
    fn test_eval_dense_mle() {
        let env = empty_env();
        // 1-var MLE [3, 7], evaluate at [0] → 3
        let v = eval_str("(eval DenseMLE (coerce (arrayof Field) DenseMLE (array 3 7)) (array (coerce Int Field 0)))", &env).unwrap();
        assert_eq!(v, Value::Field(fr(3)));
    }

    #[test]
    fn test_eval_type_mismatch() {
        let env = empty_env();
        assert!(eval_str("(eval Field (coerce (arrayof Field) DensePoly (array 1 2)) (coerce Int Field 3))", &env).is_err());
    }

    // ── Deg ──
    #[test]
    fn test_deg_dense_poly() {
        let env = empty_env();
        // p(x) = 1 + 2x + 3x^2 → degree 2
        let v = eval_str("(deg DensePoly (coerce (arrayof Field) DensePoly (array 1 2 3)))", &env).unwrap();
        assert_eq!(v, Value::Int(2));
    }

    #[test]
    fn test_deg_sparse_poly() {
        let env = empty_env();
        let v = eval_str("(deg SparsePoly (poly (ids x) (pow Field x 3)))", &env).unwrap();
        assert_eq!(v, Value::Int(3));
    }

    #[test]
    fn test_deg_type_mismatch() {
        let env = empty_env();
        assert!(eval_str("(deg Field (coerce Int Field 5))", &env).is_err());
    }

    // ── NVars ──
    #[test]
    fn test_nvars_mle() {
        let env = empty_env();
        // 2-var MLE [1,2,3,4]
        let v = eval_str("(numvars DenseMLE (coerce (arrayof Field) DenseMLE (array 1 2 3 4)))", &env).unwrap();
        assert_eq!(v, Value::Int(2));
    }

    #[test]
    fn test_nvars_uv_poly() {
        let env = empty_env();
        let v = eval_str("(numvars DensePoly (coerce (arrayof Field) DensePoly (array 1 2)))", &env).unwrap();
        assert_eq!(v, Value::Int(1));
    }

    // ── PDiv ──
    #[test]
    fn test_tpdiv() {
        let env = empty_env();
        // (x^2 + 2x + 1) / (x + 1) = (x + 1, 0)
        let v = eval_str("(div DensePoly (coerce (arrayof Field) DensePoly (array 1 2 1)) (coerce (arrayof Field) DensePoly (array 1 1)))", &env).unwrap();
        match v {
            Value::Pair(q, r) => {
                // quotient = x + 1 → coeffs [1, 1]
                let qp = q.as_polynomial().unwrap();
                assert_eq!(qp.coeffs.len(), 2);
                assert_eq!(qp.coeffs[0], fr(1));
                assert_eq!(qp.coeffs[1], fr(1));
                // remainder = 0
                let rp = r.as_polynomial().unwrap();
                assert!(rp.is_zero());
            }
            _ => panic!("expected pair"),
        }
    }

    #[test]
    fn test_pdiv_type_mismatch() {
        let env = empty_env();
        assert!(eval_str("(div SparsePoly (poly (ids x) 1) (poly (ids x) 1))", &env).is_err());
    }

    // ── Fft / Ifft ──
    #[test]
    fn test_fft_dense_poly() {
        let env = empty_env();
        // FFT of constant poly [5] over domain size 4 → [5, 5, 5, 5]
        let v = eval_str("(fft DensePoly 4 (coerce (arrayof Field) DensePoly (array 5)))", &env).unwrap();
        let arr = v.as_array().unwrap();
        assert_eq!(arr.len(), 4);
        for el in &arr {
            assert_eq!(el.as_field().unwrap(), fr(5));
        }
    }

    #[test]
    fn test_ifft_array() {
        let env = empty_env();
        // IFFT of constant evaluations [5,5,5,5] → constant poly [5]
        let v = eval_str("(ifft Array 4 (array (coerce Int Field 5) (coerce Int Field 5) (coerce Int Field 5) (coerce Int Field 5)))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.coeffs.len(), 1);
        assert_eq!(p.coeffs[0], fr(5));
    }

    #[test]
    fn test_fft_tifft_roundtrip() {
        let env = empty_env();
        // FFT then IFFT should recover the original polynomial
        let v = eval_str("(ifft Array 4 (fft DensePoly 4 (coerce (arrayof Field) DensePoly (array 1 2 3))))", &env).unwrap();
        let p = v.as_polynomial().unwrap();
        assert_eq!(p.coeffs[0], fr(1));
        assert_eq!(p.coeffs[1], fr(2));
        assert_eq!(p.coeffs[2], fr(3));
    }

    // ── Select / Store ──
    #[test]
    fn test_tselect() {
        let env = empty_env();
        let v = eval_str("(get Field (array (coerce Int Field 10) (coerce Int Field 20) (coerce Int Field 30)) 1)", &env).unwrap();
        assert_eq!(v, Value::Field(fr(20)));
    }

    #[test]
    fn test_select_out_of_bounds() {
        let env = empty_env();
        assert!(eval_str("(get Field (array (coerce Int Field 1)) 5)", &env).is_err());
    }

    #[test]
    fn test_tstore() {
        let env = empty_env();
        let v = eval_str("(set Field (array (coerce Int Field 10) (coerce Int Field 20)) 0 (coerce Int Field 99))", &env).unwrap();
        let arr = v.as_array().unwrap();
        assert_eq!(arr[0], Value::Field(fr(99)));
        assert_eq!(arr[1], Value::Field(fr(20)));
    }

    // ── AAdd ──
    #[test]
    fn test_taadd() {
        let env = empty_env();
        let v = eval_str("(add (arrayof Field) (arrayof Field) (array (coerce Int Field 1) (coerce Int Field 2)) (array (coerce Int Field 10) (coerce Int Field 20)))", &env).unwrap();
        let arr = v.as_array().unwrap();
        assert_eq!(arr[0], Value::Field(fr(11)));
        assert_eq!(arr[1], Value::Field(fr(22)));
    }

    // ── Eq ──
    #[test]
    fn test_eq_field_true() {
        let env = empty_env();
        let v = eval_str("(eq Field (coerce Int Field 42) (coerce Int Field 42))", &env).unwrap();
        assert_eq!(v, Value::Bool(true));
    }

    #[test]
    fn test_eq_field_false() {
        let env = empty_env();
        let v = eval_str("(eq Field (coerce Int Field 1) (coerce Int Field 2))", &env).unwrap();
        assert_eq!(v, Value::Bool(false));
    }

    #[test]
    fn test_eq_type_mismatch() {
        let env = empty_env();
        // Passing a DensePoly when tag says Field
        assert!(eval_str("(eq Field (coerce (arrayof Field) DensePoly (array 1 2)) (coerce Int Field 3))", &env).is_err());
    }
}
