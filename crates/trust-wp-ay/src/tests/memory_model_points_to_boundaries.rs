// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! points-to permission-boundary strengthening tests.
//!
//! These tests prove UNSAT duals for `encode_points_to` permission boundaries:
//! - full required permission (`PERM_SCALE`)
//! - zero required permission (`0`)
//! - split state cannot satisfy full requirement

use ntest::timeout;

use crate::{
    memory_model::{MemPtr, MemoryModel, PERM_SCALE},
    tests::helpers::{assert_unsat, mem_test_setup_unconstrained},
};

/// After alloc, points-to at exactly PERM_SCALE is forced.
#[test]
#[timeout(30000)]
fn alloc_forces_points_to_at_full_permission_boundary() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(123);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let full = solver.int_const(PERM_SCALE);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, full);
    let not_points_to = solver.not(points_to);
    solver.assert_term(not_points_to);

    assert_unsat(
        &mut solver,
        "NOT points_to(ptr, val, PERM_SCALE) must be UNSAT after alloc",
    );
}

/// After alloc, points-to at required permission 0 is still forced.
///
/// `encode_points_to` checks `current_perm >= required_perm`; with full
/// permission at alloc, the zero boundary must satisfy the permission guard.
#[test]
#[timeout(30000)]
fn alloc_forces_points_to_at_zero_permission_boundary() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(123);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let zero = solver.int_const(0);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, zero);
    let not_points_to = solver.not(points_to);
    solver.assert_term(not_points_to);

    assert_unsat(
        &mut solver,
        "NOT points_to(ptr, val, 0) must be UNSAT after alloc",
    );
}

/// Zero permission does not bypass value equality.
///
/// Even at the `perm = 0` boundary, points-to must still reject the wrong value.
#[test]
#[timeout(30000)]
fn zero_permission_rejects_wrong_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let correct_val = solver.int_const(123);
    let wrong_val = solver.int_const(999);
    let state = model.alloc(&mut solver, state, &ptr, correct_val);

    let zero = solver.int_const(0);
    let points_to_wrong = model.encode_points_to(&mut solver, &state, addr, wrong_val, zero);
    solver.assert_term(points_to_wrong);

    assert_unsat(
        &mut solver,
        "points_to(ptr, wrong_val, 0) must be UNSAT: zero permission does not weaken value equality",
    );
}

/// In a half-permission split state, requiring full points-to is impossible.
#[test]
#[timeout(30000)]
fn split_permission_rejects_points_to_full_boundary() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(123);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let half = solver.int_const(PERM_SCALE / 2);
    let mut split_state = state.clone();
    split_state.permissions = solver.store(split_state.permissions, addr, half);

    let full = solver.int_const(PERM_SCALE);
    let points_to_full = model.encode_points_to(&mut solver, &split_state, addr, val, full);
    solver.assert_term(points_to_full);

    assert_unsat(
        &mut solver,
        "points_to(ptr, val, PERM_SCALE) must be UNSAT when current permission is PERM_SCALE/2",
    );
}
