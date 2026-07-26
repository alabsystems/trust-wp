# Creusot Compatibility Matrix

Author: Andrew Yates <andrewyates.name@gmail.com>

This document tracks trust-wp's compatibility with Creusot syntax and features.
Goal: VISION.md Phase 6 states "Simple Creusot examples verify unchanged."

## Status Note

trust-wp is **not yet** at 100% Creusot compatibility and should not be described
as a full or drop-in replacement yet.

- Canonical committed baselines in `tests/creusot_compat/` are stale and should
  be treated as historical snapshots, not the current source of truth.
- For the current compatibility baseline, consult the live snapshot under
  `tests/creusot_compat/baseline-*.json` (headline numbers change per commit
  and are not repeated here).
- Clean `main` has moved beyond the committed baseline in several lanes;
  refresh all compatibility artifacts before publishing a headline score.
- Highest-value remaining root-cause families are:
  `cc/collections.rs`, now partitioned on clean `main` into
  map/sequence witness proof-asserts, iterator relation bridging,
  `IterMut` sort inference, and copied-adapter postconditions;
  slice/vector extraction and sort resolution (`vector/06_knights_tour.rs`);
  and reusable proof-assert closure/contradiction generation.
- Active blockers include the `cc/collections.rs` iterator/hashmap lane,
  broader ghost/proof_assert coverage (`#2209`), and remaining soundness /
  feature gaps (`#2663`, `#1296`, closures/generics follow-ups).

## Contract Attributes

| Feature | Creusot Syntax | trust-wp Status | Notes |
|---------|---------------|---------------|-------|
| Precondition | `#[requires(...)]` | Done | Full support |
| Postcondition | `#[ensures(...)]` | Done | Full support |
| Loop invariant | `#[invariant(...)]` | Done | Full support |
| Variant | `#[variant(...)]` | Partial | Loop variants and self-recursive decrease checks work; mutual recursion is rejected structurally |
| Assertion | `#[assert(...)]` | Missing | Runtime-erased assertions |
| Trusted | `#[trusted]` | Done | Skip verification |
| Open invariant | `#[open_inv_result]` | Done | Suppresses result-type invariant injection (#2564) |

## Contract Expression Forms

| Feature | Creusot Syntax | trust-wp Status | Notes |
|---------|---------------|---------------|-------|
| Result binding | `result` | Done | Postconditions and loop invariants |
| Old expression | `old(expr)` | Done | Postconditions only |
| Current value | `*v` | Done | Deref on `&mut` bindings |
| Final value | `^v` | Done | Prophecy encoding |
| View operator | `expr@` | Done | Seq model for Vec |
| Implication | `==>` | Done | Maps to `BinOp::Implies` |

## Type Support

| Feature | Creusot | trust-wp Status | Notes |
|---------|---------|---------------|-------|
| `Seq<T>` | Full | Partial | Type exists, uninterpreted funcs in ay |
| `Ghost<T>` | Full | Partial | Constructors/accessors/deref are wired through the std-spec table; runtime erasure and end-to-end ghost coverage remain incomplete (`#2209`) |
| `Snapshot<T>` | Full | Partial | Capture/inner/deref are wired through the std-spec table and sort inference normalizes snapshots into the Int-model lane; full proof_assert coverage remains incomplete (`#2209`) |
| `FSet<T>` | Full (`Set<T>`) | Done | trust-wp-std/src/logic/fset.rs (461 LOC, backed by HashSet) |
| `Mapping<K,V>` | Full | Done | trust-wp-std/src/logic/mapping.rs (327 LOC, backed by HashMap) |
| `Int` (unbounded) | Full | Partial | `Int(i128)` in trust-wp-std/src/logic/int.rs (not truly unbounded) |
| Generic types | Full | Partial | Basic monomorphization only |

## Quantifiers

| Feature | Creusot Syntax | trust-wp Status | Notes |
|---------|---------------|---------------|-------|
| Universal | `forall<x:T> expr` | Done | Parser done, ay encoding works (#178) |
| Existential | `exists<x:T> expr` | Done | Parser done, ay encoding works (#178) |
| Bounded | `forall<i:Int> 0 <= i && i < n ==> ...` | Done | Implication chaining works |

**Quantifier Implementation:**
- Parser supports `forall<x:T>` and `exists<x:T>` syntax
- ay encoding uses `fresh_var()` for proper quantifier-bound variables
- PureExpr quantifiers in contracts fully work (E-matching instantiation)
- Tests: `crates/trust-wp-ay/src/tests/quantifiers.rs`

## Specification Functions

| Feature | Creusot Attribute | trust-wp Status | Notes |
|---------|-------------------|---------------|-------|
| Logic functions | `#[logic]` | Done | Detection, declaration, calls, and axiom guards work |
| Predicates | `#[predicate]` | Done | trust-wp-macros/src/lib.rs:131 (= `#[logic]` + bool return check) |
| Trusted specs | `#[trusted]` | Done | Skip body verification |
| Law functions | `#[law]` | Done | trust-wp-macros/src/lib.rs:141 via `process_law()` |

## Ghost Code

| Feature | Creusot Syntax | trust-wp Status | Notes |
|---------|---------------|---------------|-------|
| Ghost blocks | `ghost! { ... }` | Partial | Macro validates, erasure incomplete |
| Ghost type | `Ghost<T>` | Partial | Type exists in trust-wp-std with std-spec wiring for constructors/accessors/deref |
| Ghost fields | Field wrapping | Missing | Struct ghost fields |
| Proof blocks | `proof_assert!` | Done | Macro validates and is erased at runtime; end-to-end ghost-context coverage still has open gaps (`#2209`) |

**Ghost Limitations:**
- `ghost!` macro parses correctly, and the std-spec table already handles `Ghost::new`, `Ghost::inner`, `Ghost::deref[_mut]`, `Snapshot::capture`, `Snapshot::inner`, and `Snapshot::deref`
- Sort inference normalizes `Ghost`/`Snapshot` into the Int-model lane, and logical `_ghost` method aliases exist for collection/sequence operations
- Runtime erasure and broader end-to-end ghost/proof_assert coverage are still incomplete; see `#2209`

## External Specifications

| Feature | Creusot Syntax | trust-wp Status | Notes |
|---------|---------------|---------------|-------|
| Extern specs | `extern_spec! { ... }` | Done | trust-wp-macros/src/extern_spec.rs (497 LOC) |
| Extern crate | `#[extern_crate]` | Missing | Crate-level specs |
| Impl specs | `impl ...` in extern_spec | Done | extern_spec only supports impl blocks |

## Pearlite DSL

| Feature | Creusot | trust-wp Status | Notes |
|---------|---------|---------------|-------|
| `pearlite! { }` | Full DSL | Done (Phase 1) | Spec-only expressions, 7b511f7 |
| Closure specs | `#[..] \|x\| ...` | Done | Fn/FnMut/FnOnce specs wired in std_specs/table/string_sync.rs |
| Model access | `@expr` | Done | Via `View` encoding |

## Standard Library Specs (trust-wp-std)

| Type | Creusot Coverage | trust-wp Status | Notes |
|------|-----------------|---------------|-------|
| `Option<T>` | Full | Done | 15 wired / 15 defined (all specs connected) |
| `Result<T,E>` | Full | Done | 14 wired / 14 defined (all specs connected) |
| `Vec<T>` | Full | Done | 24 wired / 24 defined (all specs connected) |
| `String` | Partial | Partial | 7 specs wired + str len/is_empty |
| `Box<T>` | Full | Missing | Heap allocation specs |
| `Rc<T>`, `Arc<T>` | Full | Done | Rc (4 methods), Arc (5 methods) wired in std_specs/table/string_sync.rs |
| `Cell<T>`, `RefCell<T>` | Full | Done | Cell (3 methods), RefCell (3 methods) wired in std_specs/table/string_sync.rs |
| `Clone` traits | Full | Partial | `trust-wp-std/src/std/clone.rs`; primitive and shared-pointer clone paths are wired today, but generic trait parity is incomplete |
| `cmp` traits | Full | Partial | Generic `PartialEq` / `PartialOrd` trait-method fallback is wired in `std_specs/table/cmp.rs` |
| `Duration` | Partial | Partial | Covered in Creusot's shared `std/time.rs`; trust-wp wires Duration constructors, arithmetic, and comparisons in `std_specs/table/time.rs` |
| `Instant` | Partial | Partial | Covered in Creusot's shared `std/time.rs`; trust-wp wires Instant time arithmetic and comparisons in `std_specs/table/time.rs` |
| Iterator traits/adapters | Full | Partial | `trust-wp-std/src/std/iter/` covers `empty`, `once`, `repeat`, `range`, `fuse`, `cloned`, `copied`, and Vec iterator entry points; many adapters remain open (`#2170`, `#2217`) |
| `mem` ops | Full | Partial | `replace`, `swap`, and `take` are wired in `std_specs/table/mem_clone_default.rs`; broader `mem` parity is still incomplete |
| `ops` traits | Full | Partial | Closure-spec traits plus `Deref` / `DerefMut` exist in `trust-wp-std/src/std/ops.rs`, but broader operator-trait parity is still incomplete |
| Primitive types | Partial | Partial | `trust-wp-std/src/std/primitives.rs` models numeric/bool/char behavior; driver wiring covers clone/default plus selected primitive operations |
| Raw pointer ops | Full | Partial | `trust-wp-std/src/std/ptr.rs` plus `std_specs/table/ptr_slice.rs` wire `addr` and `is_null`; full pointer parity remains incomplete |
| Slice `[T]` | Full | Partial | Index access only |
| `HashMap<K,V>` | Full | Done | 14 methods wired in std_specs/table/collections.rs |

## Verification Capabilities

| Capability | Creusot | trust-wp | Notes |
|------------|---------|--------|-------|
| Overflow checking | Via Why3 | Manual | Requires explicit bounds |
| Termination proofs | Via Why3 | Partial | Loop variants and self-recursive checks work; mutual-recursive variant ordering is not implemented yet |
| Separation logic | No | Experimental | SL encoder exists but not used in production pipeline |
| Counterexamples | Via provers | Done | ay model extraction |

## Example Compatibility

### Working Examples

```rust
// Basic arithmetic - WORKS
#[requires(x > 0)]
#[ensures(result > x)]
fn increment(x: i32) -> i32 { x + 1 }

// Mutable borrows - WORKS
#[requires(*v > i32::MIN)]
#[ensures(^v == old(*v) + 1)]
fn increment_ref(v: &mut i32) { *v += 1; }

// Loop invariants - WORKS
#[requires(n >= 0)]
#[ensures(result == n * (n + 1) / 2)]
fn sum_to(n: i32) -> i32 {
    let mut i = 0;
    let mut sum = 0;
    #[invariant(i <= n)]
    #[invariant(sum == i * (i + 1) / 2)]
    while i < n {
        i += 1;
        sum += i;
    }
    sum
}
```

### Also Working

```rust
// Quantifiers in contracts - DONE
#[ensures(forall<i:Int> 0 <= i && i < result.len() ==> result[i] == 0)]
fn zeros(n: usize) -> Vec<i32> { vec![0; n] }

// Logic functions - DONE
#[logic]
fn is_sorted(s: Seq<i32>) -> bool {
    forall<i:Int, j:Int> 0 <= i && i < j && j < s.len() ==> s[i] <= s[j]
}

// External specs - DONE
extern_spec! {
    impl<T> Vec<T> {
        #[ensures(result@ == old(self@).push_back(value))]
        fn push(&mut self, value: T);
    }
}
```

### Not Yet Working

```rust
// Ghost code - PARTIAL
fn verified_with_ghost(v: &mut Vec<i32>) {
    ghost! { proof_assert!(v@.len() > 0); }
    v.push(42);
}
```

## Migration Guide

For Creusot users migrating to trust-wp:

1. **Attribute syntax** - Identical, no changes needed
2. **Expression syntax** - `*v`, `^v`, `old()`, `@` all work
3. **Quantifiers** - Full support (parser and ay encoding work)
4. **Ghost code** - Partially special-cased today, but end-to-end support is still incomplete (`#2209`)
5. **Spec functions** - `#[logic]`, `#[predicate]`, and `#[law]` fully work
6. **External specs** - `extern_spec!` works for impl blocks (trust-wp-macros/src/extern_spec.rs)
7. **Closure specs** - `Fn`, `FnMut`, `FnOnce` specs wired in std_specs/table/string_sync.rs

## References

- Creusot docs: https://github.com/creusot-rs/creusot/tree/master/creusot/book
- Issue #150: Track Creusot compatibility
- Issue #2209: Ghost code handling remains the main Creusot compatibility blocker
- Issue #153: Logic functions (complete)
- Issue #160: Extern-spec workflow design
