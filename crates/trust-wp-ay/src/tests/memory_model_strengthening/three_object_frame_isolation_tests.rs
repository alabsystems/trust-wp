// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Three-object frame isolation: alloc A, B, C; dealloc B; verify A and C
/// are completely unaffected in domain, permissions, and heap values.
#[test]
#[timeout(30000)]
fn three_object_frame_isolation_dealloc_middle() {
    let (model, mut solver, state) = mem_test_setup();

    let addr_a = solver.int_const(10);
    let addr_b = solver.int_const(20);
    let addr_c = solver.int_const(30);
    let ptr_a = MemPtr::new(addr_a);
    let ptr_b = MemPtr::new(addr_b);
    let ptr_c = MemPtr::new(addr_c);
    let val_a = solver.int_const(1);
    let val_b = solver.int_const(2);
    let val_c = solver.int_const(3);

    // Alloc all three
    let state = model.alloc(&mut solver, state, &ptr_a, val_a);
    let state = model.alloc(&mut solver, state, &ptr_b, val_b);
    let state = model.alloc(&mut solver, state, &ptr_c, val_c);

    // Dealloc B (middle)
    let state = model.dealloc(&mut solver, state, &ptr_b);

    // Assert A is still fully alive
    let in_dom_a = model.in_domain(&mut solver, &state, &ptr_a);
    solver.assert_term(in_dom_a);
    let full_a = model.has_full_permission(&mut solver, &state, &ptr_a);
    solver.assert_term(full_a);
    let loaded_a = model.load(&mut solver, &state, &ptr_a);
    let eq_a = solver.eq(loaded_a, val_a);
    solver.assert_term(eq_a);

    // Assert C is still fully alive
    let in_dom_c = model.in_domain(&mut solver, &state, &ptr_c);
    solver.assert_term(in_dom_c);
    let full_c = model.has_full_permission(&mut solver, &state, &ptr_c);
    solver.assert_term(full_c);
    let loaded_c = model.load(&mut solver, &state, &ptr_c);
    let eq_c = solver.eq(loaded_c, val_c);
    solver.assert_term(eq_c);

    // Assert B is NOT in domain
    let in_dom_b = model.in_domain(&mut solver, &state, &ptr_b);
    let not_b = solver.not(in_dom_b);
    solver.assert_term(not_b);

    assert_sat(
        &mut solver,
        "three-object frame: dealloc B must preserve A and C state",
    );
}

/// Three-object frame: claiming A's value differs after dealloc B must be UNSAT.
/// This is the strengthened dual — the model FORCES A to retain its value.
#[test]
#[timeout(30000)]
fn three_object_frame_isolation_dealloc_middle_forces_value_preserved() {
    let (model, mut solver, state) = mem_test_setup();

    let addr_a = solver.int_const(10);
    let addr_b = solver.int_const(20);
    let addr_c = solver.int_const(30);
    let ptr_a = MemPtr::new(addr_a);
    let ptr_b = MemPtr::new(addr_b);
    let ptr_c = MemPtr::new(addr_c);
    let val_a = solver.int_const(1);
    let val_b = solver.int_const(2);
    let val_c = solver.int_const(3);

    let state = model.alloc(&mut solver, state, &ptr_a, val_a);
    let state = model.alloc(&mut solver, state, &ptr_b, val_b);
    let state = model.alloc(&mut solver, state, &ptr_c, val_c);
    let state = model.dealloc(&mut solver, state, &ptr_b);

    // Try to claim A's value is NOT 1 (should be UNSAT — value is forced)
    let loaded_a = model.load(&mut solver, &state, &ptr_a);
    let wrong = solver.int_const(999);
    let eq_wrong = solver.eq(loaded_a, wrong);
    solver.assert_term(eq_wrong);

    assert_unsat(
        &mut solver,
        "dealloc B must force A to retain value 1 (not 999)",
    );
}
