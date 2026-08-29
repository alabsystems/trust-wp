// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Store-after-dealloc soundness and permission boundary tests.
//!
//! These tests verify critical soundness properties at the dealloc boundary:
//! - Store after dealloc must NOT restore domain or permissions
//! - Store after dealloc DOES update the heap (design property)
//! - has_full_permission boundary: PERM_SCALE ± 1 behavior
//!
//! Part of #901 (tool_quality, assertion strengthening)

use ntest::timeout;

use crate::{
    memory_model::{MemPtr, MemoryModel, PERM_SCALE},
    tests::helpers::{assert_unsat, mem_test_setup, mem_test_setup_unconstrained},
};

// ============================================================================
// Store-after-dealloc soundness tests
// ============================================================================

/// Store after dealloc must NOT restore domain membership.
///
/// This is critical for soundness: if storing to a freed location could
/// implicitly restore domain membership, use-after-free checks would be
/// bypassable. Only `alloc` can add locations to the domain.
#[test]
#[timeout(30000)]
fn store_after_dealloc_does_not_restore_domain() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let val2 = solver.int_const(200);

    let state = model.alloc(&mut solver, state, &ptr, val1);
    let state = model.dealloc(&mut solver, state, &ptr);

    // Store after dealloc — updates heap but NOT domain/permissions
    let state = model.store(&mut solver, state, &ptr, val2);

    // Domain must still be false after store
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    assert_unsat(
        &mut solver,
        "store after dealloc must not restore domain membership (only alloc can)",
    );
}

/// Store after dealloc must NOT restore permissions.
///
/// Companion to `store_after_dealloc_does_not_restore_domain`: verifies that
/// the permissions array is also not implicitly modified by `store`.
#[test]
#[timeout(30000)]
fn store_after_dealloc_does_not_restore_permissions() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let val2 = solver.int_const(200);

    let state = model.alloc(&mut solver, state, &ptr, val1);
    let state = model.dealloc(&mut solver, state, &ptr);
    let state = model.store(&mut solver, state, &ptr, val2);

    let has_perm = model.has_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_perm);

    assert_unsat(
        &mut solver,
        "store after dealloc must not restore permissions (store only modifies heap)",
    );
}

/// Store after dealloc DOES update the heap value.
///
/// This verifies the positive side: store always writes to heap, even after
/// dealloc. The stored value is observable if you load without domain check.
/// This documents the model's design: the value is there, but inaccessible
/// through the safety predicate.
#[test]
#[timeout(30000)]
fn store_after_dealloc_updates_heap_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let val2 = solver.int_const(200);

    let state = model.alloc(&mut solver, state, &ptr, val1);
    let state = model.dealloc(&mut solver, state, &ptr);
    let state = model.store(&mut solver, state, &ptr, val2);

    // The heap should contain val2 (store worked on heap)
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq_v2 = solver.eq(loaded, val2);
    let not_eq_v2 = solver.not(eq_v2);
    solver.assert_term(not_eq_v2);

    assert_unsat(
        &mut solver,
        "store after dealloc must update heap: load(ptr) != val2 is UNSAT",
    );
}

/// Store after dealloc must NOT make points-to satisfiable.
///
/// Even though store updates the heap, the domain remains false after dealloc.
/// Since `encode_points_to` requires `in_domain(loc)`, the full points-to
/// predicate must remain UNSAT after store-after-dealloc.
#[test]
#[timeout(30000)]
fn store_after_dealloc_points_to_still_unsatisfiable() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let val2 = solver.int_const(200);

    let state = model.alloc(&mut solver, state, &ptr, val1);
    let state = model.dealloc(&mut solver, state, &ptr);
    let state = model.store(&mut solver, state, &ptr, val2);

    // Even though heap has val2, domain is false so points-to fails
    let perm = solver.int_const(1);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val2, perm);
    solver.assert_term(points_to);

    assert_unsat(
        &mut solver,
        "points-to must be UNSAT after dealloc even when heap is updated by store",
    );
}

// ============================================================================
// has_full_permission boundary tests
// ============================================================================

/// PERM_SCALE - 1 must NOT satisfy has_full_permission.
///
/// has_full_permission uses `eq(perm, PERM_SCALE)`, not `ge`. This test
/// catches off-by-one errors where the predicate might accept near-full
/// permissions. Together with `alloc_forces_exact_perm_scale` from
/// memory_model_strengthening.rs, this establishes the exact boundary.
#[test]
#[timeout(30000)]
fn perm_scale_minus_one_rejects_has_full_permission() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Set permission to PERM_SCALE - 1
    let almost_full = solver.int_const(PERM_SCALE - 1);
    let mut almost_state = state.clone();
    almost_state.permissions = solver.store(almost_state.permissions, addr, almost_full);

    let has_full = model.has_full_permission(&mut solver, &almost_state, &ptr);
    solver.assert_term(has_full);

    assert_unsat(
        &mut solver,
        "PERM_SCALE - 1 must NOT satisfy has_full_permission (eq check, not ge)",
    );
}

/// PERM_SCALE + 1 must NOT satisfy has_full_permission.
///
/// Verifies the upper boundary: over-full permission is also rejected by
/// the equality check. This would catch a hypothetical ge-based implementation.
#[test]
#[timeout(30000)]
fn perm_scale_plus_one_rejects_has_full_permission() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Set permission to PERM_SCALE + 1 (over-full)
    let over_full = solver.int_const(PERM_SCALE + 1);
    let mut over_state = state.clone();
    over_state.permissions = solver.store(over_state.permissions, addr, over_full);

    let has_full = model.has_full_permission(&mut solver, &over_state, &ptr);
    solver.assert_term(has_full);

    assert_unsat(
        &mut solver,
        "PERM_SCALE + 1 must NOT satisfy has_full_permission (eq check rejects over-full)",
    );
}
