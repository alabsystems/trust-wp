// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Permission exactly zero must NOT satisfy has_permission (boundary: perm > 0).
///
/// has_permission checks `perm > 0`. At the exact boundary (perm == 0), the
/// predicate must be false. This catches off-by-one errors in the permission
/// comparison (e.g., if someone changes > to >=).
#[test]
#[timeout(30000)]
fn zero_permission_forces_has_permission_false() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Manually set permission to exactly 0
    let zero = solver.int_const(0);
    let mut zero_perm_state = state.clone();
    zero_perm_state.permissions = solver.store(zero_perm_state.permissions, addr, zero);

    let has_perm = model.has_permission(&mut solver, &zero_perm_state, &ptr);
    solver.assert_term(has_perm);

    assert_unsat(
        &mut solver,
        "perm==0 must not satisfy has_permission (boundary: perm > 0, not >=)",
    );
}

/// Permission exactly 1 must satisfy has_permission (boundary: perm > 0).
///
/// Companion to `zero_permission_forces_has_permission_false`: at perm==1,
/// the predicate must be true. Together they verify the exact > 0 boundary.
#[test]
#[timeout(30000)]
fn one_permission_forces_has_permission_true() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Manually set permission to exactly 1
    let one = solver.int_const(1);
    let mut one_perm_state = state.clone();
    one_perm_state.permissions = solver.store(one_perm_state.permissions, addr, one);

    // has_permission should be true (1 > 0)
    let has_perm = model.has_permission(&mut solver, &one_perm_state, &ptr);
    let not_has_perm = solver.not(has_perm);
    solver.assert_term(not_has_perm);

    assert_unsat(
        &mut solver,
        "NOT has_permission at perm==1 must be UNSAT (1 > 0 is true)",
    );
}
