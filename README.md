# arkΣΠ — Algebraic Language & Runtime

A 40-node algebraic intermediate language with generic arithmetic, indexed Σ/Π loops, FFT/IFFT, and explicit representation conversions over BLS12-381 field/curve/polynomial types, optimized via egg's equality saturation with type-analysis-guarded rewrite rules.

## Language Overview

arkΣΠ uses S-expression syntax (native egg format). Expressions are parsed into `RecExpr<ArkLang>` and evaluated by a type-dispatching runtime interpreter.

### Node Types (40 total)

| Category | Nodes | Syntax |
|----------|-------|--------|
| **Generic Arithmetic** (6) | `add`, `neg`, `mul`, `inv`, `scale`, `pow` | `(add x y)`, `(scale c P)` |
| **Evaluation & Queries** (3) | `eval`, `deg`, `nvars` | `(eval p x)`, `(deg p)` |
| **Polynomial Constructors** (7) | `poly:duv`, `poly:suv`, `poly:dmle`, `poly:smle`, `poly:mv`, `ids`, `poly` | `(poly:duv 1 2 3)`, `(poly (ids x) ...)` |
| **Poly-Specific** (3) | `pdiv`, `pmod`, `fix` | `(pdiv p q)` |
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

## Rewrite Rules (30 total)

| Category | Count | Examples |
|----------|-------|---------|
| Algebra | 11 | `add-comm`, `mul-dist`, `scale-one`, `double-neg` |
| Eval distribution | 4 | `eval-add`, `eval-neg`, `eval-scale`, `eval-mul` |
| Σ/Π transforms | 6 | `sigma-unroll-1/2/3`, `sigma-dist-add`, `pi-unroll-1/2` |
| Guarded Σ | 3 | `sigma-factor-scale`, `sigma-factor-mul`, `sigma-fusion` |
| Conversion | 6 | `densify-sparsify`, `as-uv-as-mle`, `ifft-fft`, `fft-ifft` |

Guarded rules use `TypeAnalysis` (egg `Analysis` trait) to track free variables per e-class. Factor extraction only fires when the scalar is independent of the loop variable.

## Building

```bash
cargo build --release
cargo test --release       # 187 tests (120 lib + 38 algebraic laws + 29 property)
cargo run --release        # 68 demo tests
```

## Test Suite

- **120 unit tests**: evaluator, language parsing, rewrite rules, type analysis, guarded conditions, FFT/IFFT, symbolic poly
- **38 algebraic law tests**: rewrite rule soundness, optimizer round-trip, guard necessity, cross-type laws, FFT roundtrip
- **29 property tests**: field/curve/polynomial ring axioms, array theory, Σ-MSM linearity
- **68 demo tests**: comprehensive integration coverage
