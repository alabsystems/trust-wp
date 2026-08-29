# Formal Proof: BaseMemoryModel Separation Logic Invariants

**Date:** 2026-02-03
**Refreshed:** 2026-03-21
**Author:** Andrew Yates <andrewyates.name@gmail.com>
**Issue:** #369, #2627
**Location:** `../src/memory_model/base/mod.rs`
**Tests:** `../src/memory_model/base/tests.rs` and related `memory_model*` slices

## Summary

This document records the current `BaseMemoryModel` separation-logic
invariants for the reference/test-harness implementation in
`../src/memory_model/base/mod.rs`.

Production verification formulas are encoded by `AYEncoder`, but the unit tests
in `../src/memory_model/base/tests.rs` and the `memory_model*` test slices exercise the
same array-based model. The current implementation establishes:

1. Points-to predicates with fractional permissions
2. Separating conjunction via domain disjointness
3. Memory-safety properties such as double-free and use-after-free detection
4. Permission conservation and boundary preservation

## Encoding Definitions

The `BaseMemoryModel` uses three SMT arrays:

- **heap**: `Array<Int, Int>` - maps locations to values
- **domain**: `Array<Int, Int>` - tracks allocated locations (`1` = allocated, `0` = not)
- **permissions**: `Array<Int, Int>` - stores permission values (`0..PERM_SCALE`, currently `0..100`)

`domain` uses `Array<Int, Int>` instead of `Array<Int, Bool>` because the
solver path for `Array(Int, Bool)` is not reliable in the targeted QF_AUFLIA
fragment (#1603).

### Notation

- `H[l]` = `select(heap, l)` - value at location `l`
- `D[l]` = `select(domain, l)` - allocation marker at location `l`
- `P[l]` = `select(permissions, l)` - stored permission at location `l`
- `l |-> v @ p` = points-to assertion (location `l` stores `v` with required permission `p`)
- `phi * psi` = separating conjunction

---

## Theorem 1: Points-To Encoding Soundness

**Statement:** The current `encode_points_to(mem, l, v, p)` helper represents
the intended points-to assertion for the test-harness memory model.

**Definition (Current Helper Semantics):**
```
l |-> v @ p  ≡  D[l] = 1 ∧ H[l] = v ∧ P[l] ≥ p ∧ 0 ≤ P[l] ≤ PERM_SCALE
```

This matches the current helper implementation exactly. Requested permission
well-formedness (`p >= 0`) remains a caller-side obligation; the helper
constrains the stored permission, not the requested term.

**Implementation:**
```rust
fn encode_points_to(solver, mem, loc, val, perm) -> Term {
    let dom_val = solver.select(mem.domain, loc);
    let one = solver.int_const(1);
    let in_dom = solver.eq(dom_val, one);

    let heap_val = solver.select(mem.heap, loc);
    let val_eq = solver.eq(heap_val, val);

    let current_perm = solver.select(mem.permissions, loc);
    let perm_ge = solver.ge(current_perm, perm);

    let perm_scale = solver.int_const(PERM_SCALE);
    let perm_bounded = solver.le(current_perm, perm_scale);
    let neg_one = solver.int_const(-1);
    let perm_non_neg = solver.gt(current_perm, neg_one);

    solver.and(
        solver.and(solver.and(in_dom, val_eq), perm_ge),
        solver.and(perm_bounded, perm_non_neg),
    )
}
```

**Proof:**
1. The helper converts domain membership into the exact-marker predicate `D[l] = 1`
2. It conjoins value equality `H[l] = v`
3. It requires `P[l] ≥ p`, allowing partial-ownership queries
4. It additionally constrains the stored permission into the valid range `0 ≤ P[l] ≤ PERM_SCALE`
5. SMT array select/store axioms provide the required functional interpretation ∎

**Soundness consequences:**
- If `D[l] != 1`, the assertion is unsatisfiable
- If `H[l] != v`, the assertion is unsatisfiable
- If `P[l] < p`, the assertion is unsatisfiable
- If `P[l] < 0` or `P[l] > PERM_SCALE`, the assertion is unsatisfiable

**Boundary note:** Negative requested permissions are not rejected by a direct
`p >= 0` conjunct here; that boundary is documented separately by
`encode_points_to_negative_permission_boundary`
(`../src/tests/algorithm_audit/memory_and_sep_logic.rs:45`).

---

## Theorem 2: Separating Conjunction Soundness

**Statement:** For two resource assertions with pointwise domain predicates
`Dphi` and `Dpsi`, the helper `encode_sep_conj` enforces non-overlap at the
current access point.

**Definition (Pointwise QF form):**
```
phi * psi  =>  !(Dphi && Dpsi)
```

**Implementation:**
```rust
fn encode_sep_conj(solver, left_domain, right_domain) -> Term {
    let both = solver.and(left_domain, right_domain);
    solver.not(both)
}
```

**Proof:**
1. Heap disjointness requires that the same access point cannot belong to both resource footprints
2. In the helper, that condition is encoded as `!(left_domain && right_domain)`
3. The implementation returns exactly that formula ∎

**Limitation:** This is the QF pointwise form only. Full quantified disjointness
would require an AUFLIA encoding such as `forall x. !(D1[x] && D2[x])`, which
is intentionally out of scope for `BaseMemoryModel::encode_sep_conj`.

---

## Theorem 3: Allocation/Deallocation Consistency

**Statement:** The `alloc` and `dealloc` operations maintain consistent domain,
heap, and permission state.

### Lemma 3.1: Allocation Establishes Domain Membership

**Statement:** After `alloc(mem, ptr, val)`:
- `D[ptr.addr] = 1`
- `H[ptr.addr] = val`
- `P[ptr.addr] = PERM_SCALE`

**Proof:**
```rust
fn alloc(solver, mut mem, ptr, val) -> MemState {
    let one = solver.int_const(1);
    let full_perm = solver.int_const(PERM_SCALE);
    mem.domain = solver.store(mem.domain, ptr.addr, one);
    mem.heap = solver.store(mem.heap, ptr.addr, val);
    mem.permissions = solver.store(mem.permissions, ptr.addr, full_perm);
    mem
}
```

By the SMT array axiom `select(store(A, i, v), i) = v`:
- `select(new_domain, addr) = 1`
- `select(new_heap, addr) = val`
- `select(new_permissions, addr) = PERM_SCALE` ∎

### Lemma 3.2: Deallocation Removes Domain Membership

**Statement:** After `dealloc(mem, ptr)`:
- `D[ptr.addr] = 0`
- `P[ptr.addr] = 0`

**Proof:**
```rust
fn dealloc(solver, mut mem, ptr) -> MemState {
    let zero = solver.int_const(0);
    mem.domain = solver.store(mem.domain, ptr.addr, zero);
    mem.permissions = solver.store(mem.permissions, ptr.addr, zero);
    mem
}
```

Again by `select(store(A, i, v), i) = v`:
- `select(new_domain, addr) = 0`
- `select(new_permissions, addr) = 0` ∎

---

## Theorem 4: Memory Safety Properties

### Theorem 4.1: Double-Free Detection

**Statement:** If `dealloc` requires `D[ptr] = 1` as a precondition, then
double-free is detectable as unsatisfiability.

**Proof:**
1. The first `dealloc(ptr)` stores `0` into `D[ptr]`
2. A second deallocation requires `D[ptr] = 1`
3. `D[ptr] = 0` and `D[ptr] = 1` cannot both hold ∎

**Test:** `test_double_dealloc_detection`
(`../src/memory_model/base/tests.rs:300`)

### Theorem 4.2: Use-After-Free Detection

**Statement:** If a valid access requires `D[ptr] = 1`, then use-after-free is
detectable as unsatisfiability.

**Proof:**
1. After `dealloc(ptr)`, we have `D[ptr] = 0`
2. Any valid load/store condition still requires `D[ptr] = 1`
3. The conjunction is unsatisfiable ∎

**Test:** `test_use_after_free_detection`
(`../src/memory_model/base/tests.rs:331`)

### Theorem 4.3: Dangling Pointer Detection

**Statement:** `constrain_initial_state()` forces `D[addr] = 0` and
`P[addr] = 0` for all addresses, making reads without allocation detectable.

**Proof:**
1. `init()` creates symbolic arrays, so emptiness is not automatic
2. `constrain_initial_state()` replaces `domain` and `permissions` with zero-valued `const_array`s
3. Therefore `select(domain, addr) = 0` and `select(permissions, addr) = 0` for every address
4. Any access requiring `D[addr] = 1` or positive permission contradicts that constrained state ∎

**Test:** `test_dangling_pointer_detection`
(`../src/memory_model/base/tests.rs:367`)

---

## Theorem 5: Fractional Permission Conservation

### Theorem 5.1: Permission Bounds

**Statement:** Valid stored permissions satisfy `0 ≤ P[l] ≤ PERM_SCALE`.

**Invariant:** `alloc` sets `P[l] = PERM_SCALE`; `dealloc` sets `P[l] = 0`; no
operation in this helper model increases permission above the allocated amount.

**Proof:**
1. `alloc` stores `PERM_SCALE`
2. `dealloc` stores `0`
3. Split and recombine operations are modeled by explicit array updates that
   must remain within the original permission budget
4. Therefore permission-preserving transformations must maintain
   `0 ≤ P[l] ≤ PERM_SCALE` ∎

### Theorem 5.2: Permission Transfer Soundness

**Statement:** `encode_points_to` with `perm > P[l]` is unsatisfiable.

**Proof:**
1. `encode_points_to` asserts `P[l] ≥ perm`
2. If `perm > P[l]`, then that conjunct is false
3. The full conjunction is therefore unsatisfiable ∎

**Test:** `test_permission_transfer_soundness`
(`../src/memory_model/base/tests.rs:513`)

### Theorem 5.3: Permission Split/Recombine

**Statement:** Splitting permission into smaller shares and later restoring the
full value is consistent with the original allocation budget.

**Proof:**
1. A split state writes some `p'` with `0 < p' < PERM_SCALE`
2. A recombined state writes `PERM_SCALE` back to the same location
3. Both states are consistent with the original budget established by `alloc`
4. The recombined state restores the full-permission predicate ∎

**Test:** `test_permission_split`, `test_permission_recombine`
(`../src/memory_model/base/tests.rs:446`,
`../src/memory_model/base/tests.rs:595`)

---

## Theorem 6: Store/Load Functional Semantics

**Statement:** `load(store(mem, ptr, val), ptr) = val`.

**Proof:**
```rust
fn store(solver, mut mem, ptr, val) -> MemState {
    mem.heap = solver.store(mem.heap, ptr.addr, val);
    mem
}

fn load(solver, mem, ptr) -> Term {
    solver.select(mem.heap, ptr.addr)
}
```

By the SMT array axiom `select(store(A, i, v), i) = v`,
`load(store(mem, ptr, val), ptr) = val` ∎

**Test:** `test_base_memory_model_load_store`
(`../src/memory_model/base/tests.rs:73`)

---

## Assumptions

1. **SMT Array Theory:** The proof assumes the standard `select`/`store` axioms
   for QF_AUFLIA arrays.
2. **Bounded Permission Domain:** `PERM_SCALE` is the maximum valid stored
   permission value.
3. **Quantifier-Free Fragment:** Full unbounded heap reasoning requires a
   quantified encoding outside this helper.
4. **Initial-State Discipline:** `init()` is intentionally symbolic. Callers
   that need an empty heap must use `constrain_initial_state()`.
5. **Caller-Side Permission Well-Formedness:** The requested permission term
   passed to `encode_points_to` is not itself normalized by the helper.

---

## Test Correspondence

| Theorem | Test Function(s) | File:Line |
|---------|------------------|-----------|
| 1 (Points-To) | `test_base_memory_model_encode_points_to`, `alloc_forces_points_to_at_full_permission_boundary`, `alloc_forces_points_to_at_zero_permission_boundary`, `zero_permission_rejects_wrong_value` | `../src/memory_model/base/tests.rs:194`; `../tests/memory_model_points_to_boundaries.rs:22`; `../tests/memory_model_points_to_boundaries.rs:47`; `../tests/memory_model_points_to_boundaries.rs:71` |
| 2 (Sep-Conj) | `test_base_memory_model_encode_sep_conj`, `sep_conj_is_symmetric` | `../src/memory_model/base/tests.rs:228`; `../tests/memory_model_strengthening.rs:1925` |
| 3.1 (Alloc) | `test_base_memory_model_alloc_dealloc` | `../src/memory_model/base/tests.rs:133` |
| 3.2 (Dealloc) | `test_base_memory_model_alloc_dealloc`, `test_dealloc_preserves_heap_value` | `../src/memory_model/base/tests.rs:133`; `../src/memory_model/base/tests.rs:2053` |
| 4.1 (Double-Free) | `test_double_dealloc_detection` | `../src/memory_model/base/tests.rs:300` |
| 4.2 (Use-After-Free) | `test_use_after_free_detection` | `../src/memory_model/base/tests.rs:331` |
| 4.3 (Dangling) | `test_dangling_pointer_detection`, `test_constrained_no_spurious_points_to_without_alloc`, `test_constrained_no_spurious_permission_without_alloc` | `../src/memory_model/base/tests.rs:367`; `../src/memory_model/base/tests.rs:981`; `../src/memory_model/base/tests.rs:1004` |
| 5.1 (Bounds) | `test_permission_conservation`, `dealloc_forces_exact_zero_permission`, `alloc_forces_exact_perm_scale`, `test_permission_above_perm_scale_is_unsat`, `test_permission_negative_is_unsat` | `../src/memory_model/base/tests.rs:651`; `../tests/memory_model_strengthening.rs:881`; `../tests/memory_model_strengthening.rs:910`; `../tests/sep_logic.rs:2799`; `../tests/sep_logic.rs:2836` |
| 5.2 (Transfer) | `test_permission_transfer_soundness` | `../src/memory_model/base/tests.rs:513` |
| 5.3 (Split/Recombine) | `test_permission_recombine` | `../src/memory_model/base/tests.rs:595` |
| 6 (Store/Load) | `test_base_memory_model_load_store`, `test_realloc_at_same_address_resets_state` | `../src/memory_model/base/tests.rs:73`; `../src/memory_model/base/tests.rs:1440` |

---

## Verification Commands

```bash
# Run all memory-model tests under the pinned nightly toolchain
cargo +nightly-2025-11-13 test -p trust-wp-ay --lib -- memory_model

# Run representative theorem tests
cargo +nightly-2025-11-13 test -p trust-wp-ay --lib test_base_memory_model_encode_points_to
cargo +nightly-2025-11-13 test -p trust-wp-ay --lib test_base_memory_model_encode_sep_conj
cargo +nightly-2025-11-13 test -p trust-wp-ay --lib test_double_dealloc_detection
cargo +nightly-2025-11-13 test -p trust-wp-ay --lib test_use_after_free_detection
cargo +nightly-2025-11-13 test -p trust-wp-ay --lib test_permission_transfer_soundness

# Full trust-wp-ay test suite
cargo +nightly-2025-11-13 test -p trust-wp-ay
```

---

## Conclusion

The `BaseMemoryModel` reference implementation remains aligned with its current
array encoding and the active nightly `memory_model` verification slice. The
core invariants documented here (points-to, separating conjunction, memory
safety, and permission conservation) now match the implementation and test
surface that `HEAD` actually exercises.
