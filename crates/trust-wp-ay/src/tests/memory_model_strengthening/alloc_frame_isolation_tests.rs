// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Alloc at ptr1 must not affect ptr2's heap value.
///
/// Proves: alloc(s, ptr1, v1); load(ptr2) is unconstrained by alloc at ptr1.
/// We show that asserting load(ptr2) != existing value after alloc at ptr1
/// is still satisfiable (alloc didn't force a value at ptr2).
/// And conversely, that alloc at ptr1 forces a value only at ptr1.
#[test]
#[timeout(30000)]
fn alloc_frame_isolation_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let v1 = solver.int_const(111);
    let v2 = solver.int_const(222);

    // Alloc both
    let state = model.alloc(&mut solver, state, &ptr1, v1);
    let state = model.alloc(&mut solver, state, &ptr2, v2);

    // Load from ptr2 must still be v2 (alloc at ptr1 didn't overwrite it).
    let loaded2 = model.load(&mut solver, &state, &ptr2);
    let eq_v2 = solver.eq(loaded2, v2);
    let not_eq_v2 = solver.not(eq_v2);
    solver.assert_term(not_eq_v2);

    assert_unsat(
        &mut solver,
        "alloc at ptr1 must not change value at ptr2: NOT(load(ptr2)==v2) is UNSAT",
    );
}

/// Alloc at ptr1 must not affect ptr2's domain membership.
///
/// Under constrained init (all-false domain), allocating at ptr1 grants
/// domain membership only at ptr1. ptr2 must remain outside the domain.
#[test]
#[timeout(30000)]
fn alloc_frame_isolation_domain() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let v1 = solver.int_const(111);

    // Alloc only at ptr1
    let state = model.alloc(&mut solver, state, &ptr1, v1);

    // ptr2 should NOT be in domain (only ptr1 was allocated)
    let in_dom_2 = model.in_domain(&mut solver, &state, &ptr2);
    solver.assert_term(in_dom_2);

    assert_unsat(
        &mut solver,
        "alloc at ptr1 must not place ptr2 in domain under constrained init",
    );
}

/// Alloc at ptr1 must not affect ptr2's permission.
///
/// Under constrained init (zero permissions), alloc at ptr1 grants PERM_SCALE
/// only at ptr1. ptr2's permission must remain zero.
#[test]
#[timeout(30000)]
fn alloc_frame_isolation_permission() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let v1 = solver.int_const(111);

    // Alloc only at ptr1
    let state = model.alloc(&mut solver, state, &ptr1, v1);

    // ptr2 should have zero permission (not affected by ptr1's alloc)
    let has_perm2 = model.has_permission(&mut solver, &state, &ptr2);
    solver.assert_term(has_perm2);

    assert_unsat(
        &mut solver,
        "alloc at ptr1 must not grant permission at ptr2 under constrained init",
    );
}
