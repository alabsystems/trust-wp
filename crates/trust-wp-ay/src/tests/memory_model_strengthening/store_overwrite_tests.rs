// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Store overwrite forces latest value: store(ptr, v1); store(ptr, v2); load(ptr) must equal v2.
///
/// Proves that ¬(load(store(store(s, ptr, v1), ptr, v2), ptr) == v2) is UNSAT.
/// This strengthens read-over-write for the multi-write case: the second write
/// must fully overwrite the first, not leave any residue.
#[test]
#[timeout(30000)]
fn store_overwrite_forces_latest_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let v1 = solver.int_const(100);
    let v2 = solver.int_const(200);

    // Allocate, store v1, then overwrite with v2.
    let state = model.alloc(&mut solver, state, &ptr, v1);
    let state = model.store(&mut solver, state, &ptr, v1);
    let state = model.store(&mut solver, state, &ptr, v2);

    let loaded = model.load(&mut solver, &state, &ptr);
    let eq_v2 = solver.eq(loaded, v2);
    let not_eq_v2 = solver.not(eq_v2);
    solver.assert_term(not_eq_v2);

    assert_unsat(
        &mut solver,
        "store(ptr, v1); store(ptr, v2); load(ptr) != v2 must be UNSAT",
    );
}

/// Store overwrite cannot leave first value: load after overwrite must not equal v1
/// when v1 != v2.
///
/// Proves that load(store(store(s, ptr, v1), ptr, v2), ptr) == v1 ∧ v1 ≠ v2 is UNSAT.
#[test]
#[timeout(30000)]
fn store_overwrite_rejects_stale_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let v1 = solver.int_const(100);
    let v2 = solver.int_const(200);

    let state = model.alloc(&mut solver, state, &ptr, v1);
    let state = model.store(&mut solver, state, &ptr, v1);
    let state = model.store(&mut solver, state, &ptr, v2);

    let loaded = model.load(&mut solver, &state, &ptr);
    // Assert loaded == v1 AND v1 != v2. If overwrite is correct, this is UNSAT.
    let eq_v1 = solver.eq(loaded, v1);
    let eq_v1v2 = solver.eq(v1, v2);
    let v1_ne_v2 = solver.not(eq_v1v2);
    let both = solver.and(eq_v1, v1_ne_v2);
    solver.assert_term(both);

    assert_unsat(
        &mut solver,
        "store overwrite must not leave stale first value when v1 != v2",
    );
}
