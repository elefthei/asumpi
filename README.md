# arkΣΠ — Algebraic Language & Runtime

A 47-node algebraic intermediate language with explicitly-typed arithmetic, indexed Σ/Π loops, FFT/IFFT, tuples, and explicit type coercions over BLS12-381 field/curve/polynomial types, optimized via egg's equality saturation with type-analysis-guarded rewrite rules.

## Language Overview

arkΣΠ uses S-expression syntax (native egg format). Expressions are parsed into `RecExpr<ArkLang>` and evaluated by a type-validated runtime interpreter.

### Node Types (47 total)

| Category | Nodes | Syntax |
|----------|-------|--------|
| **Typed Arithmetic** (6) | `add`, `neg`, `mul`, `inv`, `scale`, `pow` | `(add Field Field x y)`, `(scale Curve c P)` |
| **Type Tags** (11) | `Field`, `Curve`, `Int`, `Bool`, `DensePoly`, `SparsePoly`, `DenseMLE`, `SparseMLE`, `MVPoly`, `Array`, `Pair` | leaf nodes |
| **Coercion** (1) | `coerce` | `(coerce Int Field 5)` |
| **Evaluation & Queries** (3) | `eval`, `deg`, `nvars` | `(eval DensePoly p x)`, `(deg DensePoly p)` |
| **Polynomial Constructors** (7) | `poly:duv`, `poly:suv`, `poly:dmle`, `poly:smle`, `poly:mv`, `ids`, `poly` | `(poly:duv 1 2 3)`, `(poly (ids x) ...)` |
| **Poly-Specific** (2) | `pdiv`, `fix` | `(pdiv DensePoly p q)` → `Pair(quotient, remainder)` |
| **Tuples** (3) | `pair`, `fst`, `snd` | `(fst (pdiv DensePoly a b))` |
| **Indexed Sum/Product** (3) | `bound`, `Σ`, `Π` | `(Σ i 0 N body)` |
| **FFT/Domain** (3) | `domain`, `fft`, `ifft` | `(fft DensePoly 8 p)`, `(domain 4)` |
| **Array** (3) | `mkarray`, `alen`, `aadd` | `(aadd Array a b)` |
| **Array Access** (2) | `select`, `store` | `(select Field arr 1)`, `(store Field arr 0 v)` |
| **Control** (2) | `let`, `if` | `(let x 5 (mul Int Int x x))` |
| **Comparison** (1) | `eq` | `(eq Field a b)` |
| **Primitives** (2) | `Num`, `Symbol` | `42`, `x` |

### Runtime Types

| ArkType | Value Variant | Backed by |
|---------|---------------|-----------|
| `Field` | `Field` | `ark_bls12_381::Fr` |
| `Curve` | `Curve` | `ark_bls12_381::G1Projective` |
| `Int` | `Int` | `i64` |
| `DensePoly` | `Polynomial` | `ark_poly::DensePolynomial<Fr>` |
| `SparsePoly` | `SparseUVPoly` | `ark_poly::univariate::SparsePolynomial<Fr>` |
| `DenseMLE` | `MLE` | `ark_poly::DenseMultilinearExtension<Fr>` |
| `SparseMLE` | `SparseMLE` | `ark_poly::SparseMultilinearExtension<Fr>` |
| `MVPoly` | `MVPoly` | `ark_poly::multivariate::SparsePolynomial<Fr, SparseTerm>` |
| `Array` | `Array` | `Vec<Value>` |
| `Bool` | `Bool` | `bool` |

### Explicitly Typed Arithmetic

All arithmetic operations carry explicit type tags. No implicit dispatch — types are validated at evaluation time. Int auto-coerces to Field where expected.

```lisp
(add Field Field 3 7)                          ;; Field: → 10 (Int auto-coerces)
(add Curve Curve P Q)                          ;; Curve: → P + Q
(add DensePoly DensePoly (poly:duv 1 2) (poly:duv 3 4))  ;; Polynomial: → poly(4 + 6x)
(scale Curve c P)                              ;; scalar × Curve point
(mul Field Field a b)                          ;; Field multiplication
(neg DensePoly p)                              ;; Polynomial negation
(pow Field x 10)                               ;; Field exponentiation
```

### Type Coercion

Explicit coercion between compatible types via the `coerce` node. No implicit coercions (except Int→Field in validate_type).

```lisp
(coerce Int Field 5)                     ;; Int → Field
(coerce Int DensePoly 3)                 ;; Int → constant polynomial
(coerce Field SparsePoly f)              ;; Field → constant sparse poly
(coerce DensePoly SparsePoly p)          ;; dense ↔ sparse representation
(coerce DenseMLE DensePoly m)            ;; 1-var MLE → UV polynomial
```

### Indexed Σ/Π Loops

```lisp
;; MSM as Σ: Σ_{i=0}^{N-1} s_i · P_i
(Σ i 0 N (scale Curve (select Field scalars i) (select Curve points i)))

;; Product: Π_{i=0}^{2} a_i
(Π i 0 3 (select Field (mkarray a b c) i))

;; Symbolic bounds for staged computation
(let N (bound 2 100) (Σ i 0 N body))
```

### Symbolic Polynomial Constructor

Human-readable syntax for building sparse polynomials:

```lisp
;; Univariate: 3x² + 5x + 7
(poly (ids x) (mul Field Field 3 (pow Field x 2)) (mul Field Field 5 x) 7)

;; Multivariate: x² + y³ + 4
(poly (ids x y) (pow Field x 2) (pow Field y 3) 4)
```

- 1 variable → produces `SparseUVPoly`
- ≥2 variables → produces `MVPoly`

### FFT / IFFT / Evaluation Domains

```lisp
(domain 8)                                ;; 8 roots of unity
(fft DensePoly 8 (poly:duv 1 2 3))       ;; coefficient → evaluation form
(ifft Array 8 evals)                      ;; evaluation → coefficient form
(eval DensePoly (ifft Array N (fft DensePoly N p)) x)  ;; roundtrip
```

### Tuples & Polynomial Division

```lisp
(pair a b)
(fst p)                                   ;; first projection
(snd p)                                   ;; second projection
(pdiv DensePoly a b)                      ;; returns Pair(quotient, remainder)
(fst (pdiv DensePoly a b))                ;; quotient
```

### Array Operations

```lisp
(aadd Array (mkarray 1 2 3) (mkarray 4 5 6))  ;; [5, 7, 9]
(select Field arr 1)                            ;; element access with type tag
(store Field arr 0 v)                           ;; element update with type tag
```

## Rewrite Rules (29 total)

| Category | Count | Examples |
|----------|-------|---------|
| Algebra | 8 | `add-comm`, `mul-dist`, `scale-one`, `double-neg` |
| Eval distribution | 4 | `eval-add`, `eval-neg`, `eval-scale`, `eval-mul` |
| Σ/Π transforms | 6 | `sigma-unroll-1/2/3`, `sigma-dist-add`, `pi-unroll-1/2` |
| Guarded Σ/arith | 5 | `sigma-factor-scale`, `sigma-factor-mul`, `sigma-fusion`, `mul-comm`, `mul-assoc` |
| Conversion/structural | 6 | `ifft-fft`, `fst-pair`, `snd-pair`, `pair-eta`, `aadd-comm` |

Guarded rules use `TypeAnalysis` (egg `Analysis` trait) to track free variables per e-class. Factor extraction only fires when the scalar is independent of the loop variable.

## Building

```bash
cargo build --release
cargo test --release       # 283 tests (210 lib + 44 algebraic laws + 29 property)
cargo run --release        # 73 demo tests → results.json
```

Always use `--release`; arkworks crypto operations are extremely slow in debug mode.

## Test Suite

- **210 unit tests**: evaluator, language parsing, rewrite rules, type analysis, guarded conditions, FFT/IFFT, symbolic poly, tuples, coerce, typed ops
- **44 algebraic law tests**: rewrite rule soundness, optimizer round-trip, guard necessity, cross-type laws, FFT roundtrip, pdiv identity, aadd commutativity
- **29 property tests**: field/curve/polynomial ring axioms, array theory, Σ-MSM linearity
- **73 demo tests**: comprehensive integration coverage
