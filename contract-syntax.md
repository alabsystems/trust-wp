<!-- Copyright 2026 Andrew Yates -->
<!-- Author: Andrew Yates <andrewyates.name@gmail.com> -->
<!-- Licensed under the Apache License, Version 2.0 -->

# trust-wp Contract Syntax

Author: Andrew Yates <andrewyates.name@gmail.com>

This document describes the user-facing contract syntax re-exported by the
`trust-wp` facade, typically via `use trust-wp::*;`.

It covers contract attributes, specification macros, and the contract expression
grammar. The facade also re-exports support items used in contracts:

- `resolve` / `Resolve` — see [`crates/trust-wp-std/src/resolve.rs`](crates/trust-wp-std/src/resolve.rs)
- `DeepModel` — see [`crates/trust-wp-std/src/logic/model.rs`](crates/trust-wp-std/src/logic/model.rs)
- `Default` — re-exported for compatibility

## Overview

trust-wp provides these contract attributes and specification macros from the
facade:

| Attribute/Macro | Purpose | Special Forms |
|-----------------|---------|---------------|
| `#[requires(...)]` | Precondition | None |
| `#[ensures(...)]` | Postcondition | `result`, `old(...)` |
| `#[invariant(...)]` | Loop invariant | `result` |
| `#[variant(...)]` | Termination variant | None |
| `#[logic(...)]` | Specification-only function | `open`, `open(self)`, `open(crate)`, `open(super)`, `law`, `opaque`, `prophetic` |
| `#[predicate(...)]` | Bool-returning logic helper | Same modes as `#[logic(...)]` |
| `#[law]` | Open-mode logic alias | None |
| `#[opaque]` | Hide logic body or type structure | None |
| `#[check(...)]` | Enable extra verifier modes | `terminates`, `ghost` |
| `#[erasure(target)]` | Compatibility marker for runtime counterpart | target path or `_` |
| `#[trusted]` | Skip verification of function body | None |
| `ghost! { ... }` | Verification-only code block | None |
| `ghost_let!(...)` | Ghost binding helper | `ghost_let!(var = expr)`, `ghost_let!(mut var = expr)` |
| `snapshot!(expr)` | Capture value snapshot | None |
| `proof_assert!(expr)` | Verification-only assertion | None |
| `pearlite!(expr)` | Pearlite DSL expression | `x@` (view syntax) |
| `extern_spec! { ... }` | Specs for external functions | None |
| `#[bitwise_proof]` | Bitvector-mode compatibility marker | None (currently pass-through) |
| `#[maintains(...)]` | Loop-maintains compatibility marker | `#[maintains(clause)]` |
| `seq![...]` | Seq literal helper for ghost/spec contexts | `seq![a, b, c]` |

### Attribute Forms

**Recommended:** Import from the facade and use the Creusot-compatible proc
macro attributes from the `trust-wp` crate:

```rust
use trust-wp::*;

#[requires(x > 0)]
#[ensures(result > x)]
fn increment(x: i32) -> i32 {
    x + 1
}
```

The same facade also exports logic helpers such as `#[predicate]` and `#[law]`,
marker attributes such as `#[check(...)]` and `#[opaque]`, plus ghost helpers
such as `ghost!` and `ghost_let!`.

This syntax is compatible with Creusot where the underlying feature exists,
enabling code to be verified by either tool. The proc macros provide IDE
support, type checking, and syntax highlighting.

> Note: `#[invariant]` attributes support inductive loop verification with three
> checks: initialization (precondition implies invariant), preservation (invariant
> maintained across iterations), and postcondition (invariant implies ensures at
> exit). Body effects are extracted from MIR via `extract_body_effects()` in
> `mir_analysis::loops::body_effects` (in the driver crate, not included in this snapshot).

## Expression Grammar

Contract expressions are a subset of Rust expressions with specific restrictions.

### Allowed Expressions

```
contract_expr ::= binary_expr
                | unary_expr
                | paren_expr
                | if_expr
                | match_expr
                | closure_expr
                | quantifier_expr
                | literal
                | path_expr
                | call_expr
                | method_call_expr
                | field_expr
                | index_expr
                | reference_expr
                | cast_expr

binary_expr   ::= contract_expr BIN_OP contract_expr
unary_expr    ::= UNARY_OP contract_expr
paren_expr    ::= '(' contract_expr ')'
if_expr       ::= 'if' contract_expr '{' contract_expr '}' ('else' '{' contract_expr '}')?
match_expr    ::= 'match' contract_expr '{' (pattern '=>' contract_expr ',')* '}'
closure_expr  ::= ('|' params '|' | '||') contract_expr
quantifier_expr ::= ('forall' | 'exists') '<' quantifier_binding (',' quantifier_binding)* '>' contract_expr
quantifier_binding ::= IDENT (':' type_expr)?
```

### Supported Operators

**Arithmetic:**
- `+` (addition)
- `-` (subtraction)
- `*` (multiplication)
- `/` (integer division)
- `%` (modulo - SMT-LIB Euclidean semantics: result always non-negative; differs from Rust `%` for negative operands)

**Comparison:**
- `==` (equality)
- `!=` (inequality)
- `<` (less than)
- `<=` (less than or equal)
- `>` (greater than)
- `>=` (greater than or equal)

**Logical:**
- `&&` (logical AND)
- `||` (logical OR)
- `!` (logical NOT)
- `==>` (implication)

**Unary:**
- `-` (negation)
- `!` (logical NOT)

### Special Forms

#### `result` (ensures and invariants)

The `result` identifier refers to the return value of the function. It is
available in `#[ensures]` postconditions and `#[invariant]` loop invariants.
`old(...)` remains `#[ensures]`-only.

```rust
#[ensures(result > 0)]
fn positive() -> i32 { 42 }

#[ensures(result == x + 1)]
fn increment(x: i32) -> i32 { x + 1 }
```

#### `old(expr)` (ensures only)

The `old(expr)` form captures the value of `expr` at function entry,
before any modifications occur.

```rust
#[ensures(result == old(x) * 2)]
fn double(x: i32) -> i32 { x * 2 }

#[ensures(result == old(v.len()) - 1)]
fn pop_and_len(v: &mut Vec<i32>) -> usize {
    v.pop();
    v.len()
}
```

#### Mutable borrow forms (`*v`, `^v`)

For mutable references, trust-wp supports RustHorn-style forms on `&mut` bindings:

- `*v` refers to the current value of `v` at function entry.
- `^v` refers to the final value of `v` when the borrow ends (postconditions
  only).
- `old(*v)` is the same as `*v` for mutable borrows.

```rust
use trust-wp::{ensures, requires};

#[requires(*v > i32::MIN)]
#[ensures(^v == old(*v) + 1)]
fn increment_ref(v: &mut i32) {
    *v += 1;
}
```

#### Logic Function Calls

Logic function calls allow invoking `#[logic]` functions in contracts. These are
pure specification functions that have no runtime effect.

```rust
#[ensures(result == max(x, y))]
fn pick_larger(x: i32, y: i32) -> i32 { /* ... */ }

#[ensures(result == abs(x))]
fn positive(x: i32) -> i32 { /* ... */ }
```

**Syntax:**
- Simple calls: `max(x, y)`, `abs(x)`, `zero()`
- Qualified paths: `crate::specs::max(a, b)`
- Nested calls: `max(x, abs(y))`
- With expressions: `max(x + 1, y * 2)`

**Status:**
- `#[logic]` attribute: ✓ Complete (self-recursive functions supported)
- SMT encoding: ✓ Uninterpreted functions with on-demand declaration
- Self-recursive functions: ✓ Supported without `#[variant]` (mutual recursion pending)

**Limitations:**
- Mutual recursion between logic functions not yet supported
- Type parameters default to Int (type-specific sorts deferred)

#### Defining Logic Functions

Use the `#[logic]` attribute to mark pure specification helpers. Logic
functions are erased at runtime and are only available to contracts.

```rust
use trust-wp::logic;

#[logic]
fn max(x: i32, y: i32) -> i32 {
    if x >= y { x } else { y }
}
```

**Requirements:**
- No `mut` binding patterns (e.g., `mut x: T`); `&mut` references are allowed
- No `async` or `unsafe`
- Self-recursive calls are supported; mutual recursion is not yet supported

#### `#[predicate(...)]`

Use `#[predicate]` for bool-returning logic helpers. It accepts the same mode
arguments as `#[logic(...)]`, but the function must return `bool`.

```rust
use trust-wp::predicate;

#[predicate]
fn is_non_negative(x: i32) -> bool {
    x >= 0
}
```

#### `#[law]`

`#[law]` is a Creusot-compatible alias for `#[logic(open)]`. Use it when the
defining body should stay visible to callers as an axiom source.

```rust
use trust-wp::{ensures, law};

#[law]
fn triple(x: i32) -> i32 {
    x + x + x
}

#[ensures(result == triple(x))]
fn triple_runtime(x: i32) -> i32 {
    x + x + x
}
```

#### Logic Modes

`#[logic(...)]` and `#[predicate(...)]` accept the same mode arguments:

| Form | Current behavior |
|------|------------------|
| `#[logic]` / `#[predicate]` | Default mode. Same-module callers can currently use the body; outside that scope the function is treated as opaque. |
| `#[logic(open)]` | Body is visible to all callers. |
| `#[logic(open(self))]` | Same-module callers can use the body; outside that module the function is treated as opaque. |
| `#[logic(open(crate))]`, `#[logic(open(super))]` | Accepted syntax, currently normalized to open behavior. |
| `#[logic(law)]` | Alias for open-mode visibility. `#[law]` emits the same mode. |
| `#[logic(opaque)]` | Explicit alias for the default opaque behavior. |
| `#[logic(prophetic)]` | Accepted syntax and currently emitted like open-mode axioms, but final-value-specific semantics are still partial. |

#### `#[opaque]`

`#[opaque]` hides a logic function body or type structure from callers. On
logic functions this suppresses the defining axiom even if the logic mode would
otherwise be open.

#### `#[check(...)]`

`#[check(...)]` enables additional verifier modes. The currently recognized
forms are:

- `#[check(terminates)]` - enables recursive termination checking. Recursive
  functions must provide `#[variant(...)]`, and mutual recursion is still
  rejected.
- `#[check(ghost)]` - marks a function as a ghost helper in the current driver
  and encoding pipeline.

Unknown `#[check(...)]` modes are compile-time errors.

#### `#[erasure(target)]`

`#[erasure(target)]` is currently a preserved compatibility marker that records
which runtime item a spec-enriched definition corresponds to. The marker is
accepted and preserved today, but the driver does not yet consume it.

#### `#[variant(...)]` (loops)

Specifies a termination variant (decreasing expression) for loops. The variant
must be non-negative while the loop continues and strictly decrease each iteration.

```rust
use trust-wp::{invariant, variant};

fn sum_to_n(n: u32) -> u32 {
    let mut i = 0;
    let mut sum = 0;
    #[invariant(sum <= i * n)]
    #[variant(n - i)]
    while i < n {
        i += 1;
        sum += i;
    }
    sum
}
```

#### `#[trusted]`

Marks a function as axiomatically correct. Preconditions are checked at call
sites, but postconditions are assumed without verifying the body. Useful for
FFI wrappers or incremental verification.

```rust
use trust-wp::{ensures, requires, trusted};

#[trusted]
#[requires(s.len() > 0)]
#[ensures(result > 0)]
fn external_hash(s: &str) -> u64 {
    // Body not verified by trust-wp
    std::collections::hash_map::DefaultHasher::new().finish()
}
```

#### `ghost! { ... }`

Marks a block as ghost (verification-only) code. Ghost blocks are erased at
compile time but verified by trust-wp. They can manipulate `Ghost<T>` values.

```rust
use trust-wp::ghost;
use trust-wp_std::ghost::Ghost;

fn example(x: i32) {
    ghost! {{
        let g: Ghost<i32> = Ghost::new(x);
        // Ghost computations for proof purposes
    }};
}
```

**Note:** Ghost/Snapshot handling is still partial, but the current pipeline
already wires constructors/accessors/deref through the std-spec table,
normalizes Ghost/Snapshot sorts into the Int-model lane, and lowers logical
`_ghost` method aliases. Runtime erasure and end-to-end ghost verification
remain incomplete (`#2209`).

#### `ghost_let!(...)`

`ghost_let!` declares a ghost binding without writing the surrounding
`Ghost::new(...)` boilerplate. It currently accepts:

- `ghost_let!(var = expr)`
- `ghost_let!(mut var = expr)`

The binding is a `Ghost<T>` under verification and is erased in normal builds.

```rust
use trust-wp::ghost_let;

fn example() {
    ghost_let!(g = 41 + 1);
    ghost_let!(mut counter = 0usize);
}
```

#### `snapshot!(expr)`

Captures a value snapshot as a `Snapshot<T>` for proof purposes. The snapshot
is zero-sized at runtime and always `Copy`.

```rust
use trust-wp::snapshot;
use trust-wp_std::ghost::Snapshot;

fn example(v: &mut Vec<i32>) {
    let original_len: Snapshot<usize> = snapshot!(v.len());
    v.push(42);
    // In verification: *original_len == v.len() - 1
}
```

#### `proof_assert!(expr)`

Inserts a verification-only assertion. Unlike `assert!`, it creates an SMT
verification condition and is completely erased at runtime.

```rust
use trust-wp::proof_assert;

fn example(x: i32, y: i32) {
    let sum = x + y;
    proof_assert!(sum == x + y);
}
```

#### `pearlite!(expr)`

Embeds a specification expression using Pearlite DSL syntax. Supports `x@`
(view) syntax. Erased at compile time.

```rust
use trust-wp::pearlite;

fn example(v: &Vec<i32>) {
    pearlite! { v@.len() > 0 };
}
```

**Status:** Quantifiers (`forall`, `exists`) and implication (`==>`) are
supported in `pearlite!`. Because `pearlite!` validates with `Requires`-kind
rules, `result` and `old(...)` remain unavailable there.

#### `extern_spec! { ... }`

Attaches specifications to external functions you don't own. External specs are
trusted (not verified against the implementation).

```rust
use trust-wp::extern_spec;

extern_spec! {
    impl<T> core::option::Option::<T> {
        #[requires(self.is_some())]
        #[ensures(Some(result) == old(self))]
        fn unwrap(self) -> T;
    }
}
```

**Note:** Generic types require turbofish syntax (`Option::<T>` not `Option<T>`).

#### `#[bitwise_proof]`

Compatibility marker for bitvector-mode verification. Currently accepted as a
pass-through attribute — the proc macro preserves the annotation, but the
verifier does not yet switch to bitvector encoding. Exported from the facade
for Creusot compile-surface parity.

#### `#[maintains(...)]`

Compatibility marker for loop-maintains clauses. Accepts a required clause
argument (`#[maintains(invariant_expr)]`) and preserves the raw text as a
contract annotation. The driver does not yet desugar maintains clauses into
full contract semantics — the attribute exists for Creusot source parity.

#### `seq![...]`

Macro for constructing `Seq` literals in ghost, snapshot, and specification
contexts. `seq![a, b, c]` produces a `Seq` value usable in contracts and
logic functions.

```rust
use trust-wp::{ensures, seq};
use trust-wp_std::logic::seq::Seq;

#[ensures(result@ == seq![1, 2, 3])]
fn make_seq() -> Vec<i32> {
    vec![1, 2, 3]
}
```

### Disallowed Expressions

The following are **not** allowed in contract expressions:

| Expression | Reason |
|------------|--------|
| Assignments (`x = ...`) | Side effects |
| Loops (`loop`, `while`, `for`) | Non-termination |
| Async/await/yield | Non-determinism |
| Return/break/continue | Control flow |

> Note: `if`, `match`, blocks, and closures **are** allowed. `if` and `match`
> are encoded as ITE (if-then-else) in SMT. Blocks are allowed as containers
> for branch bodies. Closures pass through validation unchanged.

## Examples

### Preconditions

```rust
// Simple bounds check
#[requires(x > 0)]
fn positive_only(x: i32) -> i32 { x }

// Multiple conditions
#[requires(x >= 0 && x < 100)]
fn bounded(x: i32) -> i32 { x }

// Disjunction
#[requires(x == 0 || x == 1)]
fn binary_flag(x: i32) -> bool { x != 0 }

// Method calls
#[requires(v.len() > 0)]
fn first(v: &[i32]) -> i32 { v[0] }

// Field access
#[requires(p.x >= 0 && p.y >= 0)]
fn quadrant_one(p: &Point) -> bool { true }
```

### Postconditions

```rust
// Basic result constraint
#[ensures(result > 0)]
fn always_positive() -> i32 { 42 }

// Result relates to input
#[ensures(result == x + 1)]
fn increment(x: i32) -> i32 { x + 1 }

// Using old() for pre-state
#[ensures(result == old(x) * 2)]
fn double(x: i32) -> i32 { x * 2 }
```

### Combined Contracts

```rust
#[requires(x > 0)]
#[ensures(result > x)]
fn double_positive(x: i32) -> i32 { x * 2 }
```

### Conditional Expressions

`if` and `match` are allowed in contracts and encoded as ITE in SMT:

```rust
#[ensures(if x > 0 { result > 0 } else { result == 0 })]
fn abs_or_zero(x: i32) -> i32 {
    if x > 0 { x } else { 0 }
}

#[ensures(match result { Some(v) => v > 0, None => true })]
fn maybe_positive(x: i32) -> Option<i32> {
    if x > 0 { Some(x) } else { None }
}
```

### Quantified Expressions

Quantifiers are accepted directly in contract expressions:

```rust
#[requires(forall<i: i32> i >= 0 ==> i + 1 > i)]
fn quantified_precondition(x: i32) -> i32 { x }

#[ensures(exists<w: i32> w == result - x)]
fn witness(x: i32) -> i32 { x }
```

### Implication

To express "if P then Q" (logical implication), use `==>`. The `if` and
`!P || Q` forms remain equivalent alternatives when they read better in
context:

```rust
// Direct implication syntax
#[requires(x > 0 ==> y > 0)]
fn conditional(x: i32, y: i32) -> i32 { /* ... */ }

// Equivalent if-then-else form
#[requires(if x > 0 { y > 0 } else { true })]
fn conditional_if(x: i32, y: i32) -> i32 { /* ... */ }

// Equivalent boolean encoding
#[requires(!(x > 0) || y > 0)]
fn conditional_bool(x: i32, y: i32) -> i32 { /* ... */ }
```

## Error Messages

Invalid contract expressions produce compile-time errors:

```rust
// ERROR: requires: contract expressions cannot contain assignments
#[requires(x = 5)]
fn bad() {}

// ERROR: ensures: old() expects exactly 1 argument, found 2
#[ensures(result == old(x, y))]
fn also_bad(x: i32, y: i32) -> i32 { x }

// ERROR: requires: failed to parse contract: expected expression
#[requires()]
fn empty_bad() {}
```
