// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Symbolic address memory-model tests.
//!
//! All tests in `memory_model/base.rs` and `memory_model_strengthening.rs` use
//! concrete addresses (`int_const(10)`, `int_const(20)`) where ay trivially
//! knows `10 != 20`. Real programs use symbolic addresses where aliasing is
//! undecided until constraints are added.
//!
//! These tests verify the memory model under symbolic addressing and lock in
//! the symbolic array read-over-write behavior fixed upstream. See #1633, #1733.
//!
//! Part of #901 (assertion strengthening).

use ay_dpll::api::Sort;
use ntest::timeout;

use crate::{
    memory_model::{MemPtr, MemoryModel},
    tests::helpers::{assert_sat, assert_unsat, mem_test_setup, mem_test_setup_unconstrained},
};

/// With symbolic addresses, store at addr1 may or may not affect load at addr2.
///
/// When addr1 and addr2 are unconstrained, the solver can choose addr1 == addr2,
/// making the store visible.
#[test]
#[timeout(30000)]
fn symbolic_address_aliasing_store_visible() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.declare_const("addr1", Sort::Int);
    let addr2 = solver.declare_const("addr2", Sort::Int);
    let ptr1 = MemPtr::new(addr1);

    let val = solver.int_const(42);
    let state = model.store(&mut solver, state, &ptr1, val);

    // Load from addr2 and assert it equals the stored value
    let ptr2 = MemPtr::new(addr2);
    let loaded = model.load(&mut solver, &state, &ptr2);
    let eq = solver.eq(loaded, val);
    solver.assert_term(eq);

    assert_sat(
        &mut solver,
        "symbolic aliasing must be SAT (choose addr1 == addr2)",
    );
}

/// With symbolic addresses constrained to be different, alloc at addr1
/// must NOT place addr2 in domain under constrained initial state.
///
/// Correct answer is Unsat — by read-over-write-different axiom:
///   `select(store(const_array(0), addr1, 1), addr2) = select(const_array(0), addr2) = 0`
/// when `addr1 != addr2`, so `domain[addr2] == 1` is false.
#[test]
#[timeout(30000)]
fn symbolic_address_non_aliasing_domain_check() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.declare_const("addr1", Sort::Int);
    let addr2 = solver.declare_const("addr2", Sort::Int);
    let addr_eq = solver.eq(addr1, addr2);
    let neq = solver.not(addr_eq);
    solver.assert_term(neq);

    let ptr1 = MemPtr::new(addr1);
    let val = solver.int_const(42);

    // Allocate at addr1 (so domain[addr1] = 1) but NOT at addr2
    let state = model.alloc(&mut solver, state, &ptr1, val);

    // Assert addr2 is in domain — should be UNSAT (addr1 != addr2, only addr1 allocated)
    // ay-dpll incorrectly returns Sat.
    let ptr2 = MemPtr::new(addr2);
    let in_dom2 = model.in_domain(&mut solver, &state, &ptr2);
    solver.assert_term(in_dom2);

    assert_unsat(
        &mut solver,
        "symbolic non-aliasing must be UNSAT (addr1 != addr2)",
    );
}

/// Alloc at symbolic addr, then points-to at the same symbolic addr succeeds.
#[test]
#[timeout(30000)]
fn symbolic_address_alloc_then_points_to() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.declare_const("addr", Sort::Int);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(55);

    let state = model.alloc(&mut solver, state, &ptr, val);

    let perm = solver.int_const(50);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, perm);
    solver.assert_term(points_to);

    assert_sat(
        &mut solver,
        "points-to at symbolic address should hold after alloc at the same symbolic address",
    );
}

/// Alloc at symbolic addr, points-to with wrong value is UNSAT.
#[test]
#[timeout(30000)]
fn symbolic_address_points_to_wrong_value_unsat() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.declare_const("addr", Sort::Int);
    let ptr = MemPtr::new(addr);
    let correct_val = solver.int_const(55);
    let wrong_val = solver.int_const(99);

    let state = model.alloc(&mut solver, state, &ptr, correct_val);

    let perm = solver.int_const(50);
    let points_to = model.encode_points_to(&mut solver, &state, addr, wrong_val, perm);
    solver.assert_term(points_to);

    assert_unsat(
        &mut solver,
        "points-to with wrong value at symbolic address must be UNSAT",
    );
}

/// Two symbolic allocs at addr1 and addr2 (constrained different):
/// dealloc addr1 must not affect addr2's domain or value.
///
/// This tests frame independence with symbolic addresses. Unlike concrete
/// addresses where ay trivially knows `10 != 20`, symbolic addresses require
/// the solver to reason about Array theory with the `addr1 != addr2` constraint.
#[test]
#[timeout(30000)]
fn symbolic_address_frame_independence() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.declare_const("addr1", Sort::Int);
    let addr2 = solver.declare_const("addr2", Sort::Int);
    let addr_eq = solver.eq(addr1, addr2);
    let neq = solver.not(addr_eq);
    solver.assert_term(neq);

    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);
    let state = model.dealloc(&mut solver, state, &ptr1);

    // addr2 still in domain
    let in_dom2 = model.in_domain(&mut solver, &state, &ptr2);
    solver.assert_term(in_dom2);

    // addr2 still has full permission
    let full2 = model.has_full_permission(&mut solver, &state, &ptr2);
    solver.assert_term(full2);

    // addr2 value preserved
    let loaded2 = model.load(&mut solver, &state, &ptr2);
    let eq2 = solver.eq(loaded2, val2);
    solver.assert_term(eq2);

    // addr1 NOT in domain
    let in_dom1 = model.in_domain(&mut solver, &state, &ptr1);
    let not1 = solver.not(in_dom1);
    solver.assert_term(not1);

    assert_sat(
        &mut solver,
        "symbolic frame independence: dealloc addr1 must preserve addr2 state when addr1 != addr2",
    );
}

/// Constrained symbolic initial state must force domain marker = 0.
#[test]
#[timeout(30000)]
fn symbolic_constrained_init_forces_exact_zero_domain_marker() {
    let (_model, mut solver, state) = mem_test_setup();

    let addr = solver.declare_const("addr_exact_zero_dom", Sort::Int);
    let dom = solver.select(state.domain, addr);
    let zero = solver.int_const(0);
    let dom_eq_zero = solver.eq(dom, zero);
    let dom_ne_zero = solver.not(dom_eq_zero);
    solver.assert_term(dom_ne_zero);

    assert_unsat(
        &mut solver,
        "constrained symbolic init must force exact domain marker 0",
    );
}

/// Wide-pointer alloc/load at the same symbolic address must satisfy read-over-write-same.
#[test]
#[timeout(30000)]
fn symbolic_wide_pointer_load_equals_store_unsat_dual() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.declare_const("addr_wide", Sort::Int);
    let size = solver.int_const(8);
    let ptr = MemPtr {
        addr,
        meta: Some(size),
    };
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "wide-pointer load at same symbolic address must equal stored value",
    );
}
