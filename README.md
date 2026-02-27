# arkΣΠ — Algebraic Language & Runtime

A 43-node algebraic intermediate language with generic arithmetic, indexed Σ/Π loops, FFT/IFFT, tuples, and explicit representation conversions over BLS12-381 field/curve/polynomial types, optimized via egg's equality saturation with type-analysis-guarded rewrite rules.

## Language Overview

arkΣΠ uses S-expression syntax (native egg format). Expressions are parsed into `RecExpr<ArkLang>` and evaluated by a type-dispatching runtime interpreter.

### Node Types (43 total)

| Category | Nodes | Syntax |
|----------|-------|--------|
| **Generic Arithmetic** (6) | `add`, `neg`, `mul`, `inv`, `scale`, `pow` | `(add x y)`, `(scale c P)` |
| **Evaluation & Queries** (3) | `eval`, `deg`, `nvars` | `(eval p x)`, `(deg p)` |
| **Polynomial Constructors** (7) | `poly:duv`, `poly:suv`, `poly:dmle`, `poly:smle`, `poly:mv`, `ids`, `poly` | `(poly:duv 1 2 3)`, `(poly (ids x) ...)` |
| **Poly-Specific** (2) | `pdiv`, `fix` | `(pdiv p q)` → `Pair(quotient, remainder)` |
| **Tuples** (3) | `pair`, `fst`, `snd` | `(fst (pdiv a b))` |
| **Indexed Sum/Product** (3) | `bound`, `Σ`, `Π` | `(Σ i 0 N body)` |
| **Conversions** (4) | `densify`, `sparsify`, `as-uv`, `as-mle` | `(densify p)` |
| **FFT/Domain** (3) | `domain`, `fft`, `ifft` | `(fft 8 p)`, `(domain 4)` |
| **Array** (5) | `mkarray`, `select`, `store`, `alen`, `aadd` | `(aadd a b)` |
| **Control** (2) | `let`, `if` | `(let x 5 (mul x x))` |
| **Comparison** (1) | `eq` | `(eq a b)` |
| **Primitives** (2) | `Num`, `Symbol` | `42`, `x` |
| **Indexed Sum/Product** (3) | `bound`, `Σ`, `Π` | `(Σ i 0 N body)` |
| **Conversions** (4) | `densify`, `sparsify`, `as-uv`, `as-mle` | `(densify p)` |
| **FFT/Domain** (3) | `domain`, `fft`, `ifft` | `(fft 8 p)`, `(domain 4)` |
| **Array** (4) | `mkarray`, `select`, `store`, `alen` | `(select arr 1)` |
| **Control** (2) | `let`, `if` | `(let x 5 (mul x x))` |
| **Comparison** (1) | `eq` | `(eq a b)` |
| **Primitives** (2) | `Num`, `Symbol` | `42`, `x` |

### Runtime Types

| Type | Description | Backed by |
|------|-------------|-----------|
| `Field` | Finite field element | `ark_bls12_381::Fr` |
| `Curve` | Elliptic curve point | `ark_bls12_381::G1Projective` |
| `Polynomial` | Dense univariate polynomial | `ark_poly::DensePolynomial<Fr>` |
| `SparseUVPoly` | Sparse univariate polynomial | `ark_poly::univariate::SparsePolynomial<Fr>` |
| `MLE` | Dense multilinear extension | `ark_poly::DenseMultilinearExtension<Fr>` |
| `SparseMLE` | Sparse multilinear extension | `ark_poly::SparseMultilinearExtension<Fr>` |
| `MVPoly` | Sparse multivariate polynomial | `ark_poly::multivariate::SparsePolynomial<Fr, SparseTerm>` |
| `Array` | Homogeneous array | `Vec<Value>` |
| `Bool` | Boolean | `bool` |
| `Int` | Integer (indices, exponents) | `i64` |

### Generic Arithmetic

All arithmetic is type-dispatched. A single `add` works on Field, Curve, Polynomial, MLE, etc.

```lisp
(add 3 7)                          ;; Field: → 10
(add P Q)                          ;; Curve: → P + Q
(add (poly:duv 1 2) (poly:duv 3 4)) ;; Polynomial: → poly(4 + 6x)
(scale c P)                        ;; scalar × value (any type)
```

### Indexed Σ/Π Loops

```lisp
;; MSM as Σ: Σ_{i=0}^{N-1} s_i · P_i
(Σ i 0 N (scale (select scalars i) (select points i)))

;; Product: Π_{i=0}^{2} a_i
(Π i 0 3 (select (mkarray a b c) i))

;; Symbolic bounds for staged computation
(let N (bound 2 100) (Σ i 0 N body))  ;; specialize N later
```

### Conversions

```lisp
(densify (poly:suv 0 5 2 3))    ;; sparse → dense UV
(sparsify (poly:duv 5 0 3))     ;; dense → sparse UV
(as-uv (poly:dmle 1 (mkarray 3 7)))  ;; 1-var MLE → UV poly
(as-mle (poly:duv 3 4))              ;; UV poly → 1-var MLE
```

### Symbolic Polynomial Constructor

Human-readable syntax for building sparse polynomials. Terms are monomial expressions using declared formal variables; coefficients and exponents can be arbitrary expressions from the environment.

```lisp
;; Univariate: 3x² + 5x + 7
(poly (ids x) (mul 3 (pow x 2)) (mul 5 x) 7)

;; Multivariate: x² + y³ + 4
(poly (ids x y) (pow x 2) (pow y 3) 4)

;; Cross terms: 2x²y
(poly (ids x y) (mul 2 (mul (pow x 2) y)))

;; Dynamic exponent from env: x^n where n is bound elsewhere
(poly (ids x) (pow x n))
```

- 1 variable → produces `SparseUVPoly`
- ≥2 variables → produces `MVPoly`
- Equivalent to `poly:suv`/`poly:mv` but much more readable

### FFT / IFFT / Evaluation Domains

```lisp
(domain 8)                       ;; 8 roots of unity [ω⁰, ω¹, ..., ω⁷]
(fft 8 (poly:duv 1 2 3))        ;; coefficient → evaluation form
(ifft 8 evals)                   ;; evaluation → coefficient form
(fft 4 (mkarray 1 2 3))         ;; also accepts raw coefficient arrays
(eval (ifft N (fft N p)) x)     ;; roundtrip: recovers original poly
```

- `fft` accepts `Polynomial`, `SparseUVPoly`, or `Array[Field]` as input
- `ifft` returns a `Polynomial` (dense UV, trailing zeros trimmed)
- `domain` returns `Array[Field]` of N-th roots of unity via arkworks `GeneralEvaluationDomain`

### Tuples & Polynomial Division

```lisp
(pair a b)                       ;; construct pair
(fst p)                          ;; first projection
(snd p)                          ;; second projection
(pdiv (poly:duv 1 0 1) (poly:duv 1 1))  ;; returns Pair(quotient, remainder)
(fst (pdiv a b))                 ;; quotient
(snd (pdiv a b))                 ;; remainder (replaces old pmod)
```

Division identity: `a = (fst (pdiv a b)) * b + (snd (pdiv a b))` — verified by property tests.

### Array Addition

```lisp
(aadd (mkarray 1 2 3) (mkarray 4 5 6))  ;; [5, 7, 9]
(aadd (mkarray 1 2) (mkarray 10 20 30)) ;; [11, 22, 30] — shorter padded with 0
```

## Rewrite Rules (34 total)

| Category | Count | Examples |
|----------|-------|---------|
| Algebra | 11 | `add-comm`, `mul-dist`, `scale-one`, `double-neg` |
| Eval distribution | 4 | `eval-add`, `eval-neg`, `eval-scale`, `eval-mul` |
| Σ/Π transforms | 6 | `sigma-unroll-1/2/3`, `sigma-dist-add`, `pi-unroll-1/2` |
| Guarded Σ | 3 | `sigma-factor-scale`, `sigma-factor-mul`, `sigma-fusion` |
| Conversion/structural | 10 | `densify-sparsify`, `ifft-fft`, `fst-pair`, `snd-pair`, `pair-eta`, `aadd-comm` |

Guarded rules use `TypeAnalysis` (egg `Analysis` trait) to track free variables per e-class. Factor extraction only fires when the scalar is independent of the loop variable.

## Building

```bash
cargo build --release
cargo test --release       # 201 tests (131 lib + 41 algebraic laws + 29 property)
cargo run --release        # 73 demo tests
```

## Test Suite

- **131 unit tests**: evaluator, language parsing, rewrite rules, type analysis, guarded conditions, FFT/IFFT, symbolic poly, tuples, aadd
- **41 algebraic law tests**: rewrite rule soundness, optimizer round-trip, guard necessity, cross-type laws, FFT roundtrip, pdiv identity, aadd commutativity
- **29 property tests**: field/curve/polynomial ring axioms, array theory, Σ-MSM linearity
- **73 demo tests**: comprehensive integration coverage
