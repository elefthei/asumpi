# Ark-wasm Language & Runtime

A WebAssembly-like language with native algebraic types, designed for compiler optimization via equality saturation (egg). All arithmetic is backed by the arkworks library using BLS12-381.

## Language Overview

Ark-wasm uses S-expression syntax (native egg format). Expressions are parsed into `RecExpr<ArkWasmLang>` and evaluated by the runtime interpreter.

### Node Types (60 total)

| Category | Nodes | Syntax |
|----------|-------|--------|
| **Field ops** (7) | `fadd`, `fsub`, `fmul`, `fdiv`, `fneg`, `finv`, `fpow` | `(fadd x y)`, `(fneg x)`, `(fpow x 3)` |
| **Curve ops** (3) | `gadd`, `gneg`, `smul` | `(gadd P Q)`, `(smul s P)` |
| **MSM** (1) | `msm` | `(msm (mkarray s0 s1) (mkarray P0 P1))` |
| **Univariate poly** (10) | `poly`, `peval`, `padd`, `pmul`, `psub`, `pneg`, `pdiv`, `pmod`, `pdeg`, `pscale` | `(peval (poly 1 2 3) x)` |
| **Sparse UV poly** (2) | `spoly`, `speval` | `(speval (spoly 0 5 2 3) x)` |
| **MLE** (5) | `mle`, `mle-eval`, `mle-nvars`, `mle-fix`, `mle-add` | `(mle-eval (mle 2 (mkarray 1 2 3 4)) (mkarray 0 1))` |
| **Sparse MLE** (2) | `smle`, `smle-eval` | `(smle-eval (smle 2 (mkarray 0 10 3 20)) (mkarray 0 0))` |
| **Multivariate poly** (4) | `mvpoly`, `mveval`, `mvdeg`, `mvadd` | `(mveval (mvpoly 2 ...) (mkarray x0 x1))` |
| **VP Dense UV** (5) | `vp-duv-new`, `vp-duv-add-product`, `vp-duv-eval`, `vp-duv-add`, `vp-duv-deg` | See below |
| **VP Sparse UV** (5) | `vp-suv-new`, `vp-suv-add-product`, `vp-suv-eval`, `vp-suv-add`, `vp-suv-deg` | See below |
| **VP Dense MLE** (5) | `vp-dmle-new`, `vp-dmle-add-product`, `vp-dmle-eval`, `vp-dmle-add`, `vp-dmle-deg` | See below |
| **VP Sparse MLE** (5) | `vp-smle-new`, `vp-smle-add-product`, `vp-smle-eval`, `vp-smle-add`, `vp-smle-deg` | See below |
| **Array** (4) | `mkarray`, `select`, `store`, `alen` | `(select (mkarray 10 20 30) 1)` |
| **Control** (2) | `let`, `if` | `(let x 5 (fmul x x))` |
| **Other** (3) | `feq`, `Num`, `Symbol` | `(feq a b)`, `42`, `x` |

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
| `VPolyDUV` | Virtual poly (dense UV products) | `VirtualPolynomial<DensePolynomial<Fr>>` |
| `VPolySUV` | Virtual poly (sparse UV products) | `VirtualPolynomial<SparseUVPolynomial<Fr>>` |
| `VPolyDMLE` | Virtual poly (dense MLE products) | `VirtualPolynomial<DenseMultilinearExtension<Fr>>` |
| `VPolySMLE` | Virtual poly (sparse MLE products) | `VirtualPolynomial<SparseMultilinearExtension<Fr>>` |
| `Array` | Typed, homogeneous array | `Vec<Value>` (all elements same type) |
| `Bool` | Boolean | Rust `bool` |
| `Int` | Integer (for indices/exponents) | `i64` |

### Array Operations (SMT Theory of Arrays)

Arrays are **typed and homogeneous** — all elements must have the same type. Mutation is modeled as **functional update**: `store` returns a new array (the old one is unchanged). This keeps all operations pure and compatible with egg's equality saturation.

```lisp
;; Create a typed array
(mkarray 10 20 30)              ;; → Array[Int(10), Int(20), Int(30)]

;; Read an element (select)
(select (mkarray 10 20 30) 1)   ;; → 20

;; Functional update (store) — returns NEW array
(store (mkarray 10 20 30) 1 99) ;; → Array[Int(10), Int(99), Int(30)]

;; Read after write
(select (store (mkarray 10 20 30) 1 99) 1)  ;; → 99

;; Original array unchanged
(select (mkarray 10 20 30) 1)               ;; → 20 (still!)

;; Array length (invariant under store)
(alen (store (mkarray 1 2 3) 0 99))         ;; → 3
```

**Type enforcement:**
- `(mkarray 1 P)` where `P` is a Curve point → **error** (heterogeneous)
- `(store (mkarray 1 2 3) 0 P)` where `P` is Curve → **error** (type mismatch)

### Egg Rewrite Rules (enabled by functional arrays)

```rust
use egg::{rewrite};

let rules = vec![
    // Core array axiom: read-after-write (same index)
    rewrite!("select-store-same"; "(select (store ?a ?i ?v) ?i)" => "?v"),

    // Store-store collapse (same index)
    rewrite!("store-store-same"; "(store (store ?a ?i ?v1) ?i ?v2)" => "(store ?a ?i ?v2)"),

    // Length invariance under store
    rewrite!("alen-store"; "(alen (store ?a ?i ?v))" => "(alen ?a)"),

    // Polynomial identities
    rewrite!("psub-self"; "(psub ?p ?p)" => "(poly 0)"),
    rewrite!("pneg-pneg"; "(pneg (pneg ?p))" => "?p"),
    rewrite!("pscale-1"; "(pscale 1 ?p)" => "?p"),
    rewrite!("pscale-0"; "(pscale 0 ?p)" => "(poly 0)"),
    rewrite!("mle-add-comm"; "(mle-add ?m1 ?m2)" => "(mle-add ?m2 ?m1)"),

    // Field arithmetic rules also apply...
    rewrite!("fadd-comm"; "(fadd ?a ?b)" => "(fadd ?b ?a)"),
    rewrite!("fmul-comm"; "(fmul ?a ?b)" => "(fmul ?b ?a)"),
];
```

### Extended Polynomial Operations

#### Univariate polynomials (dense)

Coefficients in ascending order: `(poly c0 c1 c2)` represents `c0 + c1·x + c2·x²`.

```lisp
;; Subtraction, negation
(psub (poly 3 2 1) (poly 1 1 0))  ;; → poly(2 + x + x²)
(pneg (poly 1 2 3))                ;; → poly(-1 - 2x - 3x²)

;; Division and modulus: (3 + 5x + 2x²) ÷ (1 + x)
(pdiv (poly 3 5 2) (poly 1 1))    ;; → quotient poly(1 + 2x)
(pmod (poly 3 5 2) (poly 1 1))    ;; → remainder poly(2)

;; Degree and scalar multiplication
(pdeg (poly 1 2 3))               ;; → 2
(pscale 5 (poly 1 2 3))           ;; → poly(5 + 10x + 15x²)
```

#### Multilinear extensions (MLE)

MLEs represent functions on the boolean hypercube `{0,1}^n`. Evaluations are in little-endian binary order: for `n=2`, indices `[00, 10, 01, 11]` correspond to `(x0=0,x1=0), (x0=1,x1=0), (x0=0,x1=1), (x0=1,x1=1)`.

```lisp
;; Construct MLE with 2 variables and 4 evaluations (2^2)
(mle 2 (mkarray 1 2 3 4))

;; Evaluate at a point
(mle-eval (mle 2 (mkarray 1 2 3 4)) (mkarray 0 1))  ;; → 3

;; Number of variables
(mle-nvars (mle 2 (mkarray 1 2 3 4)))  ;; → 2

;; Fix first variable (partial evaluation for sumcheck)
(mle-fix (mle 2 (mkarray 1 2 3 4)) (mkarray 1))  ;; → MLE with 1 var

;; Add two MLEs (must have same num_vars)
(mle-add m1 m2)
```

#### Multivariate polynomials (sparse)

Terms are encoded as flat arrays `[var0, pow0, var1, pow1, ...]`.

```lisp
;; Construct: 3·x0² + 2·x0·x1 in 2 variables
;; coeffs = [3, 2], terms encoded as arrays of (var_idx, power) pairs
(mvpoly 2 (mkarray 3 2) (mkarray (mkarray 0 2) (mkarray 0 1 1 1)))

;; Evaluate at point (x0=2, x1=3)
(mveval p (mkarray 2 3))  ;; → 3·4 + 2·2·3 = 24

;; Degree and addition
(mvdeg p)       ;; → 2
(mvadd p1 p2)
```

### Virtual Polynomials (Sum of Products)

A virtual polynomial represents `Σ c_i · Π_j P_ij` — a sum of products of polynomials, inspired by HyperPlonk. The generic `VirtualPolynomial<P>` struct supports four specializations:

| Type | Inner polynomial | Point type | Construction |
|------|-----------------|------------|--------------|
| `VPolyDUV` | Dense univariate | `Fr` | `(vp-duv-new nvars)` |
| `VPolySUV` | Sparse univariate | `Fr` | `(vp-suv-new nvars)` |
| `VPolyDMLE` | Dense MLE | `[Fr]` | `(vp-dmle-new nvars)` |
| `VPolySMLE` | Sparse MLE | `[Fr]` | `(vp-smle-new nvars)` |

Each type supports 5 operations: `new`, `add-product`, `eval`, `add`, `deg`.

```lisp
;; Dense UV: VP = 3·(1+2x) + 2·(x²)
(let vp (vp-duv-new 1)
  (let vp (vp-duv-add-product vp 3 (mkarray (poly 1 2)))
    (let vp (vp-duv-add-product vp 2 (mkarray (poly 0 0 1)))
      (vp-duv-eval vp 5))))  ;; → 3*11 + 2*25 = 83

;; Dense MLE: VP = 5·m1·m2 (product of two MLEs)
(vp-dmle-eval
  (vp-dmle-add-product (vp-dmle-new 1) 5
    (mkarray (mle 1 (mkarray 2 4)) (mle 1 (mkarray 1 3))))
  (mkarray 0))  ;; → 5*2*1 = 10

;; Sparse UV: VP = 2·(5+3x²) using sparse representation
(vp-suv-eval
  (vp-suv-add-product (vp-suv-new 1) 2 (mkarray (spoly 0 5 2 3)))
  2)  ;; → 2*(5+12) = 34
```

### Sparse Polynomial Types

```lisp
;; Sparse UV: specify (power, coefficient) pairs
(spoly 0 5 2 3)        ;; → 5 + 3x² (only non-zero terms)
(speval (spoly 0 5 2 3) 2)  ;; → 17

;; Sparse MLE: specify (index, value) pairs on the hypercube
(smle 2 (mkarray 0 10 3 20))  ;; 2 vars, index 0→10, index 3→20
(smle-eval (smle 2 (mkarray 0 10 3 20)) (mkarray 0 0))  ;; → 10
```

### Examples

```lisp
;; Field arithmetic
(fadd 3 7)                     ;; → 10
(fmul (fadd 3 4) (fsub 5 2))  ;; → 21

;; Polynomial evaluation: 1 + 2x + 3x² at x=5
(peval (poly 1 2 3) 5)        ;; → 86

;; Let binding
(let x 5 (fmul x x))          ;; → 25

;; MSM: s0*P0 + s1*P1
(msm (mkarray s0 s1) (mkarray p0 p1))

;; Functional array update pipeline
(let arr (mkarray 1 2 3)
  (let arr2 (store arr 1 99)
    (fadd (select arr 1) (select arr2 1))))  ;; → 2 + 99 = 101
```

## Building

```bash
cargo build --release
cargo test --release
cargo run --release    # Runs the demo/test suite
```

## Test Suite

- **75 unit tests**: field arithmetic, curve ops, MSM, polynomials (dense+sparse), MLE (dense+sparse), virtual polynomials (4 types × 5 ops), arrays, let bindings, conditionals
- **31 property-based tests** (proptest): commutativity, associativity, distributivity, inverse laws, MSM linearity, polynomial identities, array axioms, VP add commutativity, sparse-dense equivalence
- **70 integration tests**: demo runner with comprehensive coverage

All 75 library tests pass. All 70 demo tests pass.
