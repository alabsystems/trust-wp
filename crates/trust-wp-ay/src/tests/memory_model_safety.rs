// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Memory model safety boundary tests.
//!
//! Tests defense-in-depth properties of the base memory model:
//! - Constrained-init blocks raw access without alloc
//! - Two-object realloc frame isolation
//! - Dealloc domain guard prevents use-after-free
//!
//! Split from `memory_model_strengthening.rs` (file size limit #509).

use ntest::timeout;

use crate::{
    memory_model::{MemPtr, MemoryModel},
    tests::helpers::{assert_unsat, mem_test_setup},
};

// ============================================================================
// Constrained-init safety boundary tests
// ============================================================================

/// Constrained-init state blocks raw encode_points_to (no prior alloc).
///
/// This is the critical safety property: after constrain_initial_state,
/// domain is const_array(false) and permissions are const_array(0). Any
/// encode_points_to without a preceding alloc must be UNSAT because
/// in_domain(loc) == false (from const_array simplification).
#[test]
#[timeout(30000)]
fn constrained_init_blocks_points_to_without_alloc() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let val = solver.int_const(100);
    let perm = solver.int_const(1);

    // Raw encode_points_to without alloc — should be UNSAT
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, perm);
    solver.assert_term(points_to);

    assert_unsat(
        &mut solver,
        "constrained-init: encode_points_to without alloc must be UNSAT \
         (domain is const_array(false), so in_domain is structurally false)",
    );
}

/// Constrained-init state blocks has_permission without alloc.
///
/// Companion to the points-to test: even checking just permission
/// (without value/domain) must fail because permissions are const_array(0).
#[test]
#[timeout(30000)]
fn constrained_init_blocks_permission_without_alloc() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);

    // has_permission checks perm > 0; under constrained init, perm == 0
    let has_perm = model.has_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_perm);

    assert_unsat(
        &mut solver,
        "constrained-init: has_permission without alloc must be UNSAT \
         (permissions are const_array(0), so perm > 0 is structurally false)",
    );
}

// ============================================================================
// Two-object realloc frame isolation
// ============================================================================

/// Alloc A, alloc B, dealloc A, realloc A — B's heap value must be unaffected.
#[test]
#[timeout(30000)]
fn two_object_realloc_frame_isolation_heap() {
    let (model, mut solver, state) = mem_test_setup();

    let addr_a = solver.int_const(10);
    let addr_b = solver.int_const(20);
    let ptr_a = MemPtr::new(addr_a);
    let ptr_b = MemPtr::new(addr_b);
    let val_a1 = solver.int_const(111);
    let val_a2 = solver.int_const(222);
    let val_b = solver.int_const(333);

    // Alloc both objects
    let state = model.alloc(&mut solver, state, &ptr_a, val_a1);
    let state = model.alloc(&mut solver, state, &ptr_b, val_b);

    // Dealloc A, then realloc A with different value
    let state = model.dealloc(&mut solver, state, &ptr_a);
    let state = model.alloc(&mut solver, state, &ptr_a, val_a2);

    // B's heap value must be preserved through A's dealloc+realloc cycle
    let loaded_b = model.load(&mut solver, &state, &ptr_b);
    let eq_b = solver.eq(loaded_b, val_b);
    let neq_b = solver.not(eq_b);
    solver.assert_term(neq_b);

    assert_unsat(
        &mut solver,
        "realloc at ptr_a must not affect ptr_b heap value (frame isolation)",
    );
}

/// Alloc A, alloc B, dealloc A, realloc A — B's domain must be unaffected.
#[test]
#[timeout(30000)]
fn two_object_realloc_frame_isolation_domain() {
    let (model, mut solver, state) = mem_test_setup();

    let addr_a = solver.int_const(10);
    let addr_b = solver.int_const(20);
    let ptr_a = MemPtr::new(addr_a);
    let ptr_b = MemPtr::new(addr_b);
    let val_a1 = solver.int_const(111);
    let val_a2 = solver.int_const(222);
    let val_b = solver.int_const(333);

    let state = model.alloc(&mut solver, state, &ptr_a, val_a1);
    let state = model.alloc(&mut solver, state, &ptr_b, val_b);
    let state = model.dealloc(&mut solver, state, &ptr_a);
    let state = model.alloc(&mut solver, state, &ptr_a, val_a2);

    // B must still be in domain
    let in_dom_b = model.in_domain(&mut solver, &state, &ptr_b);
    let not_in_dom_b = solver.not(in_dom_b);
    solver.assert_term(not_in_dom_b);

    assert_unsat(
        &mut solver,
        "realloc at ptr_a must not remove ptr_b from domain (frame isolation)",
    );
}

/// Alloc A, alloc B, dealloc A, realloc A — B's permission must be unaffected.
#[test]
#[timeout(30000)]
fn two_object_realloc_frame_isolation_permission() {
    let (model, mut solver, state) = mem_test_setup();

    let addr_a = solver.int_const(10);
    let addr_b = solver.int_const(20);
    let ptr_a = MemPtr::new(addr_a);
    let ptr_b = MemPtr::new(addr_b);
    let val_a1 = solver.int_const(111);
    let val_a2 = solver.int_const(222);
    let val_b = solver.int_const(333);

    let state = model.alloc(&mut solver, state, &ptr_a, val_a1);
    let state = model.alloc(&mut solver, state, &ptr_b, val_b);
    let state = model.dealloc(&mut solver, state, &ptr_a);
    let state = model.alloc(&mut solver, state, &ptr_a, val_a2);

    // B must still have full permission
    let full_b = model.has_full_permission(&mut solver, &state, &ptr_b);
    let not_full_b = solver.not(full_b);
    solver.assert_term(not_full_b);

    assert_unsat(
        &mut solver,
        "realloc at ptr_a must not affect ptr_b permission (frame isolation)",
    );
}

// ============================================================================
// Dealloc blocks encode_points_to
// ============================================================================

/// After dealloc, encode_points_to must be UNSAT even though heap retains value.
///
/// This is the critical safety invariant: dealloc removes domain membership,
/// and encode_points_to requires in_domain(loc). Even though the heap array
/// still contains the pre-dealloc value (see dealloc_preserves_heap_value),
/// the domain check prevents access. If encode_points_to ever dropped the
/// domain check, this test would catch the regression.
#[test]
#[timeout(30000)]
fn dealloc_blocks_points_to_despite_retained_heap_value() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Alloc, then dealloc
    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);

    // Try to access via encode_points_to with the original value
    // This should be UNSAT because domain is now false at this address
    let perm = solver.int_const(1);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, perm);
    solver.assert_term(points_to);

    assert_unsat(
        &mut solver,
        "encode_points_to after dealloc must be UNSAT: domain is false even \
         though heap retains the value (defense-in-depth via domain check)",
    );
}

/// After dealloc, encode_points_to with zero permission is STILL UNSAT.
///
/// Edge case: even with perm=0 (ge(0, 0) is true), the domain check
/// prevents access. This verifies the domain guard is independent of the
/// permission guard.
#[test]
#[timeout(30000)]
fn dealloc_blocks_points_to_even_with_zero_permission() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);

    // Zero permission — permission check passes (0 >= 0), but domain blocks
    let zero_perm = solver.int_const(0);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, zero_perm);
    solver.assert_term(points_to);

    assert_unsat(
        &mut solver,
        "encode_points_to after dealloc with perm=0: domain guard is independent \
         of permission guard (both must hold, domain is false after dealloc)",
    );
}
