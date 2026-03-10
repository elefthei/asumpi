# Copilot Instructions — arkΣΠ

## Build & Test

```bash
cargo build --release
cargo test --release                      # full suite (232 lib + 44 algebraic + 37 property)
cargo test --release --lib <test_name>    # single unit test
cargo test --release --test algebraic_laws <test_name>  # single algebraic law test
cargo test --release --test property_tests <test_name>  # single property test
cargo run --release                       # 71 demo integration tests → results.json
```

Always use `--release`; arkworks crypto operations are extremely slow in debug mode.

## Architecture

**S-expression language on top of egg + arkworks.** The crate defines a 43-node algebraic IR (`ArkLang`) using egg's `define_language!` macro, with explicitly-typed arithmetic, a type-validating runtime interpreter, and equality-saturation optimizer over BLS12-381 field/curve/polynomial types.

### Data flow

```
S-expression string
  → egg::RecExpr<ArkLang>          (parse)
  → eval(expr, env) → Value        (interpret with type validation)
  → Runner + all_rules() → EGraph  (optimize via equality saturation)
  → Extractor → RecExpr<ArkLang>   (extract smallest equivalent)
```

### Module responsibilities

| Module | Role |
|--------|------|
| `language.rs` | `ArkLang` enum via `define_language!` — 43 node types (typed arithmetic, type tags, coerce, polynomials, Σ/Π/for loops, FFT, arrays, control flow) |
| `value.rs` | `Value` enum (11 variants: Field, Curve, Polynomial, MLE, MVPoly, SparseUVPoly, SparseMLE, Array, Pair, Bool, Int) + `ArkType` enum (with `ArrayOf(Box<ArkType>)`) + `EvalError` |
| `eval.rs` | Recursive top-down evaluator. `eval(expr, env) -> Result<Value, EvalError>`. Type-validated arithmetic with explicit type tags. Also: `specialize()` for bound-variable substitution |
| `analysis.rs` | `TypeAnalysis` (egg `Analysis` trait) — tracks type over-approximation + free variables per e-class. `IndependentOf` condition for guarded rewrites |
| `rules.rs` | 39 rewrite rules in 9 groups: `add_rules`, `arith_rules`, `sigma_rules`, `guarded_sigma_rules`, `guarded_arith_rules`, `sigma_unroll_rules`, `eval_rules`, `conversion_rules`, `fusion_rules`. Combined via `all_rules()` |
| `main.rs` | Demo binary that runs 71 integration tests and writes `results.json` |

### Key type mappings

All runtime types are backed by arkworks (BLS12-381):
- `Field` → `ark_bls12_381::Fr`
- `Curve` → `ark_bls12_381::G1Projective`
- `Polynomial` → `ark_poly::DensePolynomial<Fr>`
- `SparseUVPoly` → `ark_poly::univariate::SparsePolynomial<Fr>`
- `MLE` / `SparseMLE` → `ark_poly::{Dense,Sparse}MultilinearExtension<Fr>`
- `MVPoly` → `ark_poly::multivariate::SparsePolynomial<Fr, SparseTerm>`

## Conventions

### Explicitly typed arithmetic
All arithmetic ops (`add`, `mul`, `neg`, etc.) carry explicit type tags: `(add Field Field a b)`, `(mul DensePoly DensePoly p q)`. Scalar multiplication uses `(mul Field T scalar obj)` — `scale` was absorbed into `mul`. Dot products and Hadamard products are expressed compositionally via `Σ` and `for` (no dedicated nodes). Parameterized types like `(arrayof Field)` are supported for array operations. The evaluator validates types at runtime via `validate_type()`.

### Type coercion
No implicit coercions except Int→Field (in `validate_type`). All other conversions require explicit `(coerce Src Dst val)`. The coerce lattice supports: identity, Int/Field→polynomial embedding, dense↔sparse representation, MLE↔poly domain changes, Array→DensePoly (coefficients), Array→DenseMLE (evaluations). Scalar multiplication uses `(mul Field T scalar obj)` — `scale` was absorbed into `mul`.

### Polynomial construction
Dense polynomials: `(coerce (arrayof Field) DensePoly (array 1 2 3))` — coefficients as array.
Dense MLEs: `(coerce (arrayof Field) DenseMLE (array 1 0 0 0))` — evaluations, num_vars inferred from log₂(len).
Sparse polys: `(poly (ids x) ...)` — symbolic constructor with monomial terms.
Multivariate: `(poly (ids x y) ...)` — 2+ variables produces MVPoly.

### Guarded rewrite rules
Loop-invariant factor extraction uses `IndependentOf` — a custom egg `Condition` that checks free-variable sets from `TypeAnalysis`. A rewrite like `(Σ ?i ?lo ?hi (mul Field ?T ?c ?f)) => (mul Field ?T ?c (Σ ?i ?lo ?hi ?f))` only fires when `?c` has no free-variable dependency on `?i`.

### Evaluation is top-down recursive
Not bottom-up over `RecExpr`'s flat vector. This is intentional — `let` scoping and `if` laziness require it. Shared subexpressions may evaluate multiple times; correctness over efficiency.

### Int vs Field distinction
`Num(i64)` evaluates to `Value::Int`, not `Value::Field`. The `as_field()` helper auto-coerces Int→Fr. `validate_type()` allows Int where Field is expected. This keeps integer indices working for array `get`/`set` while still allowing concise expressions like `(add Field Field 3 7)` without explicit coercion.

### Negative integer → field conversion
Use `int_to_fr(n: i64)` from `value.rs` which handles negative values via field negation (`-Fr::from((-n) as u64)`), not direct casting.

### Test helpers
Shared test utilities live in `tests/common/mod.rs`: `fr(u64)` for field elements, `eval_str(&str, &Env)` for parse+eval, `env_with_fields(...)` for building environments. Property tests use `proptest` with arkworks types generated via seeded RNG.

### Stream fusion
The `fusion_rules` group (5 rules) eliminates intermediate arrays produced by `for` comprehensions. Key rewrites: `sigma-for-fusion` and `for-for-fusion` fuse Σ/for over `(get T (for ...) i)` into the body directly; `get-for` indexes into a comprehension via `let`; `get-set-same` is read-after-write elimination; `sigma-neg-body` floats negation out of Σ.

### Rule naming
Rewrite rule string identifiers use kebab-case (e.g., `"sigma-factor-scale"`, `"add-comm"`, `"ifft-fft"`, `"sigma-for-fusion"`).
