// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Memory model edge-case tests: boundary conditions not covered by the inline
//! `base.rs` test module or the dedicated strengthening/soundness files.
//!
//! Tests:
//! - Store at unallocated address does not grant domain or permissions
//! - Zero-permission boundary for `has_permission`
//! - Double-alloc (without dealloc) overwrites completely
//!
//! Re: #901 memory_verification audit

use ntest::timeout;

use crate::{
    memory_model::{MemPtr, MemoryModel},
    tests::helpers::{assert_sat, assert_unsat, mem_test_setup},
};

/// Store at an unallocated address must NOT make it appear in domain.
///
/// `store` only modifies the heap array, not domain or permissions.
/// If a caller stores to an address without first allocating, the domain
/// and permission arrays must remain unaffected. This catches any
/// hypothetical bug where `store` accidentally updates domain.
#[test]
#[timeout(30000)]
fn store_at_unallocated_does_not_grant_domain() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    // Store without allocating first
    let state = model.store(&mut solver, state, &ptr, val);

    // addr must NOT be in domain: constrain_initial_state set domain to
    // const_array(0), and store only touches heap.
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    assert_unsat(
        &mut solver,
        "store at unallocated address must NOT make it in-domain",
    );
}

/// Store at an unallocated address must NOT grant any permission.
///
/// UNSAT dual for permissions: `store` does not touch the permissions array.
#[test]
#[timeout(30000)]
fn store_at_unallocated_does_not_grant_permission() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.store(&mut solver, state, &ptr, val);
    let has_perm = model.has_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_perm);

    assert_unsat(
        &mut solver,
        "store at unallocated address must NOT grant any permission",
    );
}

/// `has_permission` must return false (UNSAT) when permission is exactly 0.
///
/// Boundary test for the lower edge: `has_permission` checks `perm > 0`,
/// so exactly 0 must be rejected. Complements `test_almost_full_permission_is_not_full`
/// which tests the upper boundary.
#[test]
#[timeout(30000)]
fn zero_permission_has_no_permission() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);

    // After constrain_initial_state, permissions are const_array(0).
    // has_permission checks perm > 0, so this must be false.
    let has_perm = model.has_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_perm);

    assert_unsat(
        &mut solver,
        "zero permission must NOT satisfy has_permission (lower boundary)",
    );
}

/// Minimal positive permission (1) must satisfy `has_permission`.
///
/// SAT dual for the zero-permission boundary test. Confirms that the
/// `perm > 0` check in `has_permission` accepts the smallest valid value.
#[test]
#[timeout(30000)]
fn minimal_permission_satisfies_has_permission() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);

    // alloc sets permission to PERM_SCALE, manually set to 1 for boundary test
    let one = solver.int_const(1);
    let mut state_mod = state;
    state_mod.permissions = solver.store(state_mod.permissions, addr, one);
    let has_perm = model.has_permission(&mut solver, &state_mod, &ptr);
    solver.assert_term(has_perm);

    assert_sat(
        &mut solver,
        "minimal permission (1) must satisfy has_permission (lower boundary SAT dual)",
    );
}

/// Double-alloc without dealloc: second alloc must leave address in domain
/// with full permission and the new value.
///
/// This is different from `test_alloc_then_store_overwrites_value` because
/// alloc also writes domain and permissions. A double-alloc at the same
/// address should leave the address in domain with full permission and the
/// new value — the second alloc dominates.
#[test]
#[timeout(30000)]
fn double_alloc_overwrites_sat() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let val2 = solver.int_const(200);

    // Double alloc: alloc(val1) then alloc(val2) without dealloc
    let state = model.alloc(&mut solver, state, &ptr, val1);
    let state = model.alloc(&mut solver, state, &ptr, val2);

    // Must be in domain
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    // Must have full permission
    let has_full = model.has_full_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_full);

    // Must see the second value
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val2);
    solver.assert_term(eq);

    assert_sat(
        &mut solver,
        "double alloc must leave address in domain with full permission and new value",
    );
}

/// Double-alloc UNSAT dual: first alloc's value must NOT be observable
/// after second alloc.
///
/// Proves that the second alloc deterministically overwrites the first.
#[test]
#[timeout(30000)]
fn double_alloc_overwrites_old_value_unsat() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let old_val = solver.int_const(100);
    let new_val = solver.int_const(200);

    let state = model.alloc(&mut solver, state, &ptr, old_val);
    let state = model.alloc(&mut solver, state, &ptr, new_val);

    let loaded = model.load(&mut solver, &state, &ptr);
    let eq_old = solver.eq(loaded, old_val);
    solver.assert_term(eq_old);

    assert_unsat(
        &mut solver,
        "double alloc: second alloc must overwrite first — load==old must be UNSAT",
    );
}
