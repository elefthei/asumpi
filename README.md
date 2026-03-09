# arkΣΠ — Algebraic Language & Runtime

A 43-node algebraic intermediate language with explicitly-typed arithmetic, indexed Σ/Π loops, FFT/IFFT, tuples, and explicit type coercions over BLS12-381 field/curve/polynomial types, optimized via egg's equality saturation with type-analysis-guarded rewrite rules.

## Language Overview

arkΣΠ uses S-expression syntax (native egg format). Expressions are parsed into `RecExpr<ArkLang>` and evaluated by a type-validated runtime interpreter.

### Node Types (43 total)

| Category | Nodes | Syntax |
|----------|-------|--------|
| **Typed Arithmetic** (6) | `add`, `neg`, `mul`, `inv`, `pow`, `coerce` | `(add Field Field x y)`, `(mul Field Curve 3 P)` |
| **Inner Product** (1) | `dot` | `(dot (arrayof Field) (arrayof Field) a b)` |
| **Type Tags** (12) | `Field`, `Curve`, `Int`, `Bool`, `DensePoly`, `SparsePoly`, `DenseMLE`, `SparseMLE`, `MVPoly`, `Array`, `Pair`, `arrayof` | `Field`, `(arrayof Field)` |
| **Evaluation & Queries** (3) | `eval`, `deg`, `numvars` | `(eval DensePoly p x)`, `(deg DensePoly p)` |
| **Symbolic Constructors** (3) | `ids`, `poly`, `mle` | `(poly (ids x) 5 (mul Field Field 3 (pow Field x 2)))` |
| **Poly-Specific** (2) | `div`, `fix` | `(div DensePoly p q)` → `Pair(quotient, remainder)` |
| **Tuples** (3) | `pair`, `fst`, `snd` | `(fst (div DensePoly a b))` |
| **Indexed Sum/Product** (3) | `bound`, `Σ`, `Π` | `(Σ i 0 N body)` |
| **FFT/Domain** (3) | `domain`, `fft`, `ifft` | `(fft DensePoly 8 p)`, `(domain 4)` |
| **Array** (4) | `array`, `length`, `get`, `set` | `(array 1 2 3)`, `(get Field arr 1)` |
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
| `ArrayOf(T)` | `Array` | `Vec<Value>` (parameterized) |
| `Bool` | `Bool` | `bool` |

### Explicitly Typed Arithmetic

All arithmetic operations carry explicit type tags. No implicit dispatch — types are validated at evaluation time. Int auto-coerces to Field where expected.

```lisp
(add Field Field 3 7)                          ;; Field: → 10 (Int auto-coerces)
(add Curve Curve P Q)                          ;; Curve: → P + Q
(mul DensePoly DensePoly p q)                  ;; Polynomial multiplication
(mul Field Curve 3 P)                          ;; Scalar × Curve (was "scale")
(mul Curve Field P 3)                          ;; Commutative: same result
(add (arrayof Field) (arrayof Field) a b)      ;; Element-wise array addition
(neg DensePoly p)                              ;; Polynomial negation
(pow Field x 10)                               ;; Field exponentiation
```

### Dot Product (Inner Product)

Computes `Σ mul(a_i, b_i)`. Works for any element types where `mul` is defined.

```lisp
(dot (arrayof Field) (arrayof Field) a b)      ;; Σ a_i * b_i → Field
(dot (arrayof Curve) (arrayof Field) Ps ss)    ;; MSM: Σ s_i * P_i → Curve
(dot (arrayof DensePoly) (arrayof Field) ps cs) ;; Σ c_i * p_i → DensePoly
```

### Hadamard (Element-wise) Product

Element-wise multiplication via `(mul (arrayof A) (arrayof B) a b)`.

```lisp
(mul (arrayof Field) (arrayof Field) a b)      ;; [a_0*b_0, a_1*b_1, ...]
(mul (arrayof Field) (arrayof Curve) ss Ps)    ;; [s_0*P_0, s_1*P_1, ...]
```

### Type Coercion

Explicit coercion between compatible types via the `coerce` node. No implicit coercions (except Int→Field in validate_type).

```lisp
;; Scalar embeddings
(coerce Int Field 5)                           ;; Int → Field
(coerce Int DensePoly 3)                       ;; Int → constant polynomial
(coerce Field SparsePoly f)                    ;; Field → constant sparse poly

;; Representation changes
(coerce DensePoly SparsePoly p)                ;; dense ↔ sparse
(coerce DenseMLE DensePoly m)                  ;; 1-var MLE → UV polynomial

;; Array → polynomial construction
(coerce (arrayof Field) DensePoly (array 1 2 3))    ;; coefficients → DensePoly (1 + 2x + 3x²)
(coerce (arrayof Field) DenseMLE (array 1 0 0 0))   ;; evaluations → DenseMLE (num_vars = log₂(len))
```

### Symbolic Polynomial Constructor

Human-readable syntax for building sparse polynomials from monomial terms:

```lisp
;; Univariate: 3x² + 5x + 7 → SparseUVPoly
(poly (ids x) (mul Field Field 3 (pow Field x 2)) (mul Field Field 5 x) 7)

;; Multivariate: x² + y³ + 4 → MVPoly
(poly (ids x y) (pow Field x 2) (pow Field y 3) 4)
```

- 1 variable → produces `SparseUVPoly`
- ≥2 variables → produces `MVPoly`

### Indexed Σ/Π Loops

```lisp
;; MSM as Σ: Σ_{i=0}^{N-1} s_i · P_i
(Σ i 0 N (mul Field Curve (get Field scalars i) (get Curve points i)))

;; Product: Π_{i=0}^{2} a_i
(Π i 0 3 (get Field (array a b c) i))

;; Symbolic bounds for staged computation
(let N (bound 2 100) (Σ i 0 N body))
```

### FFT / IFFT / Evaluation Domains

```lisp
(domain 8)                                     ;; 8 roots of unity
(fft DensePoly 8 (coerce (arrayof Field) DensePoly (array 1 2 3)))
(ifft Array 8 evals)                           ;; evaluation → coefficient form
(eval DensePoly (ifft Array N (fft DensePoly N p)) x)  ;; roundtrip
```

### Tuples & Polynomial Division

```lisp
(pair a b)
(fst p)                                        ;; first projection
(snd p)                                        ;; second projection
(div DensePoly a b)                            ;; returns Pair(quotient, remainder)
(fst (div DensePoly a b))                      ;; quotient
```

### Array Operations

```lisp
(array 1 2 3)                                  ;; construct array
(get Field arr 1)                              ;; element access with type tag
(set Field arr 0 v)                            ;; element update with type tag
(add (arrayof Field) (arrayof Field) a b)      ;; element-wise addition
(length arr)                                   ;; array length
```

## Rewrite Rules (28 total)

| Category | Function | Count | Examples |
|----------|----------|-------|---------|
| Algebra (add) | `add_rules` | 3 | `add-comm`, `add-assoc`, `add-neg` |
| Algebra (arith) | `arith_rules` | 8 | `double-neg`, `mul-dist`, `mul-one`, `mul-zero`, `mul-scalar-dist` |
| Eval distribution | `eval_rules` | 4 | `eval-add`, `eval-neg`, `eval-scale`, `eval-mul` |
| Σ transforms | `sigma_rules` | 1 | `sigma-dist-add` |
| Σ unrolling | `sigma_unroll_rules` | 2 | `sigma-unroll-2`, `sigma-unroll-3` |
| Guarded Σ | `guarded_sigma_rules` | 1 | `sigma-fusion-add` |
| Guarded arith | `guarded_arith_rules` | 2 | `sigma-factor-scalar`, `sigma-factor-mul` |
| Conversion/structural | `conversion_rules` | 7 | `ifft-fft`, `fst-pair`, `snd-pair`, `pair-eta`, coerce roundtrips |

Guarded rules use `TypeAnalysis` (egg `Analysis` trait) to track free variables per e-class. Factor extraction only fires when the scalar is independent of the loop variable.

`mul` absorbs the former `scale` operation: `(mul Field T scalar obj)` replaces `(scale T scalar obj)`.

## Building

```bash
cargo build --release
cargo test --release       # 298 tests (217 lib + 44 algebraic laws + 37 property)
cargo run --release        # 73 demo tests → results.json
```

Always use `--release`; arkworks crypto operations are extremely slow in debug mode.

## Test Suite

- **217 unit tests**: evaluator, language parsing, rewrite rules, type analysis, guarded conditions, FFT/IFFT, symbolic poly, tuples, coerce, typed ops, dot product, Hadamard product
- **44 algebraic law tests**: rewrite rule soundness, optimizer round-trip, guard necessity, cross-type laws, FFT roundtrip, div identity
- **37 property tests**: field/curve/polynomial ring axioms, array theory, Σ-MSM linearity, dot commutativity/linearity/zero/unit, Hadamard commutativity/associativity/unit/zero
- **73 demo tests**: comprehensive integration coverage
