# arkΣΠ — Algebraic Language & Runtime

A 43-node algebraic intermediate language with explicitly-typed arithmetic, indexed Σ/Π loops, FFT/IFFT, tuples, and explicit type coercions over BLS12-381 field/curve/polynomial types, optimized via egg's equality saturation with type-analysis-guarded rewrite rules.

## Language Overview

arkΣΠ uses S-expression syntax (native egg format). Expressions are parsed into `RecExpr<ArkLang>` and evaluated by a type-validated runtime interpreter.

### Node Types (43 total)

| Category | Nodes | Syntax |
|----------|-------|--------|
| **Typed Arithmetic** (6) | `add`, `neg`, `mul`, `inv`, `pow`, `coerce` | `(add Field Field x y)`, `(mul Field Curve 3 P)` |
| **Type Tags** (12) | `Field`, `Curve`, `Int`, `Bool`, `DensePoly`, `SparsePoly`, `DenseMLE`, `SparseMLE`, `MVPoly`, `Array`, `Pair`, `arrayof` | `Field`, `(arrayof Field)` |
| **Evaluation & Queries** (3) | `eval`, `deg`, `numvars` | `(eval DensePoly p x)`, `(deg DensePoly p)` |
| **Symbolic Constructors** (3) | `ids`, `poly`, `mle` | `(poly (ids x) 5 (mul Field Field 3 (pow Field x 2)))` |
| **Poly-Specific** (2) | `div`, `fix` | `(div DensePoly p q)` → `Pair(quotient, remainder)` |
| **Tuples** (3) | `pair`, `fst`, `snd` | `(fst (div DensePoly a b))` |
| **Indexed Sum/Product/Comprehension** (4) | `bound`, `Σ`, `Π`, `for` | `(Σ i 0 N body)`, `(for i 0 N body)` |
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
(neg DensePoly p)                              ;; Polynomial negation
(pow Field x 10)                               ;; Field exponentiation
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

### Indexed Σ/Π/For Loops

```lisp
;; MSM as Σ: Σ_{i=0}^{N-1} s_i · P_i
(Σ i 0 N (mul Field Curve (get Field scalars i) (get Curve points i)))

;; Product: Π_{i=0}^{2} a_i
(Π i 0 3 (get Field (array a b c) i))

;; Array comprehension: [body[i=0], ..., body[i=N-1]]
(for i 0 N (mul Field Field (get Field as i) (get Field bs i)))

;; Symbolic bounds for staged computation
(let N (bound 2 100) (Σ i 0 N body))
```

Dot products and Hadamard (element-wise) products are expressed compositionally — no dedicated nodes:

```lisp
;; Dot product: Σ a_i * b_i → Field
(Σ i 0 n (mul Field Field (get Field as i) (get Field bs i)))

;; Hadamard product: [a_0*b_0, a_1*b_1, ...] → Array
(for i 0 n (mul Field Field (get Field as i) (get Field bs i)))

;; Element-wise array addition
(for i 0 n (add Field Field (get Field as i) (get Field bs i)))
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
(length arr)                                   ;; array length
```

## Rewrite Rules (39 total)

| Category | Function | Count | Examples |
|----------|----------|-------|---------|
| Algebra (add) | `add_rules` | 3 | `add-comm`, `add-assoc`, `add-neg` |
| Algebra (arith) | `arith_rules` | 8 | `double-neg`, `mul-dist`, `mul-one`, `mul-zero`, `mul-scalar-dist` |
| Eval distribution | `eval_rules` | 4 | `eval-add`, `eval-neg`, `eval-mul-scalar`, `eval-mul` |
| Σ transforms | `sigma_rules` | 1 | `sigma-dist-add` |
| Σ unrolling | `sigma_unroll_rules` | 2 | `sigma-unroll-2`, `sigma-unroll-3` |
| Guarded Σ | `guarded_sigma_rules` | 1 | `sigma-fusion-add` |
| Guarded arith | `guarded_arith_rules` | 2 | `sigma-factor-scalar`, `sigma-factor-mul` |
| Conversion/structural | `conversion_rules` | 9 | `ifft-fft`, `fst-pair`, `snd-pair`, `pair-eta`, coerce roundtrips |
| Stream fusion | `fusion_rules` | 9 | `sigma-for-fusion`, `for-for-fusion`, `get-for`, `get-set-same`, `set-set-same`, `set-get-noop`, `length-set`, `length-for`, `sigma-neg-body` |

Guarded rules use `TypeAnalysis` (egg `Analysis` trait) to track free variables per e-class. Factor extraction only fires when the scalar is independent of the loop variable.

### Stream Fusion

The `fusion_rules` group eliminates intermediate arrays produced by `for` comprehensions, analogous to stream fusion in functional compilers:

```lisp
;; Σ-for fusion: eliminates intermediate array in Σ(for(...))
(Σ i 0 n (get T (for i 0 n body) i))  →  (Σ i 0 n body)

;; for-for fusion: collapses nested comprehension
(for i 0 n (get T (for i 0 n body) i))  →  (for i 0 n body)

;; Index into comprehension → let substitution
(get T (for i 0 n body) k)  →  (let i k body)

;; Get/set laws
(get T (set T arr i v) i)  →  v           ;; read-after-write
(set T (set T arr i v1) i v2)  →  (set T arr i v2)  ;; last write wins
(set T arr i (get T arr i))  →  arr       ;; no-op write

;; Length laws
(length (set T arr i v))  →  (length arr)  ;; set preserves length
(length (for i lo hi body))  →  (add Int Int hi (neg Int lo))

;; Negation floats out of Σ
(Σ i 0 n (neg T f))  →  (neg T (Σ i 0 n f))
```

`mul` absorbs the former `scale` operation: `(mul Field T scalar obj)` replaces `(scale T scalar obj)`.

## Building

```bash
cargo build --release
cargo test --release       # 313 tests (232 lib + 44 algebraic laws + 37 property)
cargo run --release        # 71 demo tests → results.json
```

Always use `--release`; arkworks crypto operations are extremely slow in debug mode.

## Test Suite

- **232 unit tests**: evaluator, language parsing, rewrite rules, type analysis, guarded conditions, FFT/IFFT, symbolic poly, tuples, coerce, typed ops, for comprehension, stream fusion
- **44 algebraic law tests**: rewrite rule soundness, optimizer round-trip, guard necessity, cross-type laws, FFT roundtrip, div identity
- **37 property tests**: field/curve/polynomial ring axioms, array theory, Σ-MSM linearity, for comprehension properties
- **71 demo tests**: comprehensive integration coverage
