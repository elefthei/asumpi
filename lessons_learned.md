# Lessons Learned — Experiment 3: Ark-wasm Language & Runtime

### DensePolynomial coeffs access
- **What happened**: Tried to use `p.coeffs()` as a method call on `DensePolynomial<Fr>`. Compiler error: "field, not a method".
- **What worked**: `DensePolynomial` exposes coefficients as a public field `p.coeffs` (no parentheses), not a method. The `DenseUVPolynomial` trait provides a `coeffs()` method, but it takes `self` by value. For comparison, use the field directly.
- **System/software context**: ark-poly v0.5, Rust edition 2021.

### egg define_language! variant naming
- **What happened**: Wanted to name a variant `Vec` for vector construction, but this conflicts with `std::vec::Vec` in some contexts.
- **What worked**: Named the variant `MkVec` in Rust code while using `"mkvec"` as the S-expression operator string. The S-expression string is what users interact with; the Rust variant name is internal only.
- **System/software context**: egg 0.9, Rust edition 2021.

### Int vs Field auto-coercion for integer literals
- **What happened**: Initially had `Num(i64)` evaluate directly to `Value::Field(Fr::from(n))`. This broke vector indexing: `(vget v 0)` failed because `as_int()` on a `Field` value doesn't work.
- **What worked**: `Num(i64)` evaluates to `Value::Int(n)`. The `as_field()` method on `Value` auto-coerces `Int` to `Fr` via `Fr::from(n as u64)`. This way, `(fadd 1 2)` works (both coerce to Fr), and `(vget v 0)` works (stays as Int).
- **System/software context**: Design decision for the ark-wasm evaluator.

### Top-down vs bottom-up evaluation for RecExpr
- **What happened**: Egg's `RecExpr` stores nodes as a flat vector where each node references earlier nodes. The natural evaluation strategy is bottom-up (visit each node once in order). However, `let` bindings require scoped environments, and `if` requires lazy evaluation of branches.
- **What worked**: Used top-down recursive evaluation (start from root, recurse into children). This handles let scoping and lazy if correctly. The tradeoff is that shared subexpressions may be evaluated multiple times, but correctness is prioritized over efficiency at this stage.
- **System/software context**: egg 0.9 RecExpr, Rust.

### Negative integers in field element conversion
- **What happened**: Converting negative `i64` to `Fr` via `Fr::from(n as u64)` wraps around incorrectly for negative values.
- **What worked**: Implemented `int_to_fr(n: i64)` that uses `-Fr::from((-n) as u64)` for negative values. This correctly computes the additive inverse in the field.
- **System/software context**: ark-ff v0.5, BLS12-381 Fr.

### proptest with arkworks types
- **What happened**: `proptest` doesn't natively support generating `Fr` or `G1Projective` values.
- **What worked**: For `Fr`, generate random `u64` values and convert via `Fr::from(u64)`. For `G1Projective`, generate a random `u64` seed and use `StdRng::seed_from_u64(seed)` with `G1Projective::rand(&mut rng)`. This covers sufficient randomness for property testing.
- **System/software context**: proptest 1.x, ark-ff v0.5, ark-ec v0.5.
