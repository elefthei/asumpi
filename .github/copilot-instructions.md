# Copilot Instructions — arkΣΠ

## Build & Test

```bash
cargo build --release
cargo test --release                      # full suite (131 lib + 41 algebraic + 29 property)
cargo test --release --lib <test_name>    # single unit test
cargo test --release --test algebraic_laws <test_name>  # single algebraic law test
cargo test --release --test property_tests <test_name>  # single property test
cargo run --release                       # 73 demo integration tests → results.json
```

Always use `--release`; arkworks crypto operations are extremely slow in debug mode.

## Architecture

**S-expression language on top of egg + arkworks.** The crate defines a 43-node algebraic IR (`ArkLang`) using egg's `define_language!` macro, with a type-dispatching runtime interpreter and equality-saturation optimizer over BLS12-381 field/curve/polynomial types.

### Data flow

```
S-expression string
  → egg::RecExpr<ArkLang>          (parse)
  → eval(expr, env) → Value        (interpret)
  → Runner + all_rules() → EGraph  (optimize via equality saturation)
  → Extractor → RecExpr<ArkLang>   (extract smallest equivalent)
```

### Module responsibilities

| Module | Role |
|--------|------|
| `language.rs` | `ArkLang` enum via `define_language!` — 43 node types (arithmetic, polynomials, Σ/Π loops, FFT, arrays, control flow) |
| `value.rs` | `Value` enum (11 variants: Field, Curve, Polynomial, MLE, MVPoly, SparseUVPoly, SparseMLE, Array, Pair, Bool, Int) + `EvalError` |
| `eval.rs` | Recursive top-down evaluator. `eval(expr, env) -> Result<Value, EvalError>`. Generic arithmetic dispatches on Value type. Also: `specialize()` for bound-variable substitution |
| `analysis.rs` | `TypeAnalysis` (egg `Analysis` trait) — tracks type over-approximation + free variables per e-class. `IndependentOf` condition for guarded rewrites |
| `rules.rs` | 34 rewrite rules in 5 groups: `algebra_rules`, `eval_rules`, `sigma_rules`, `guarded_sigma_rules`, `conversion_rules`. Combined via `all_rules()` |
| `main.rs` | Demo binary that runs 73 integration tests and writes `results.json` |

### Key type mappings

All runtime types are backed by arkworks (BLS12-381):
- `Field` → `ark_bls12_381::Fr`
- `Curve` → `ark_bls12_381::G1Projective`
- `Polynomial` → `ark_poly::DensePolynomial<Fr>`
- `SparseUVPoly` → `ark_poly::univariate::SparsePolynomial<Fr>`
- `MLE` / `SparseMLE` → `ark_poly::{Dense,Sparse}MultilinearExtension<Fr>`
- `MVPoly` → `ark_poly::multivariate::SparsePolynomial<Fr, SparseTerm>`

## Conventions

### Generic arithmetic pattern
All arithmetic ops (`add`, `mul`, `neg`, `scale`) are type-dispatched through helper functions (`value_add`, `value_mul`, etc.) in `eval.rs`. When adding a new type, extend these dispatch functions and add the corresponding `as_<type>()` extractor to `Value`.

### Guarded rewrite rules
Loop-invariant factor extraction (e.g., pulling a scalar out of a Σ loop) uses `IndependentOf` — a custom egg `Condition` that checks free-variable sets from `TypeAnalysis`. A rewrite like `(Σ ?i ?lo ?hi (scale ?c ?f)) => (scale ?c (Σ ?i ?lo ?hi ?f))` only fires when `?c` has no free-variable dependency on `?i`.

### Evaluation is top-down recursive
Not bottom-up over `RecExpr`'s flat vector. This is intentional — `let` scoping and `if` laziness require it. Shared subexpressions may evaluate multiple times; correctness over efficiency.

### Int vs Field distinction
`Num(i64)` evaluates to `Value::Int`, not `Value::Field`. The `as_field()` helper auto-coerces Int→Fr. This keeps integer indices working for array `select`/`store` while still allowing implicit coercion in arithmetic contexts.

### Negative integer → field conversion
Use `int_to_fr(n: i64)` from `value.rs` which handles negative values via field negation (`-Fr::from((-n) as u64)`), not direct casting.

### Test helpers
Shared test utilities live in `tests/common/mod.rs`: `fr(u64)` for field elements, `eval_str(&str, &Env)` for parse+eval, `env_with_fields(...)` for building environments. Property tests use `proptest` with arkworks types generated via seeded RNG.

### Rule naming
Rewrite rule string identifiers use kebab-case (e.g., `"sigma-factor-scale"`, `"add-comm"`, `"ifft-fft"`).
