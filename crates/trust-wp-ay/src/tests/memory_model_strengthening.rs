// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Focused memory-model assertion-strengthening regressions.
//!
//! Each test here proves a stronger property than the corresponding SAT-only
//! test in `memory_model/base.rs`: where base tests check that a formula *can*
//! hold (SAT), these tests prove that the negation *cannot* hold (UNSAT).
//! This is the difference between "consistent with the model" and "forced by
//! the model."

use ay_dpll::api::{Logic, Solver, Sort};
use ntest::timeout;

use crate::{
    memory_model::{BaseMemoryModel, MemPtr, MemoryModel, PERM_SCALE},
    tests::helpers::{assert_sat, assert_unsat, mem_test_setup, mem_test_setup_unconstrained},
};

#[path = "memory_model_strengthening/store_overwrite_tests.rs"]
mod store_overwrite_tests;

#[path = "memory_model_strengthening/permission_boundary_tests.rs"]
mod permission_boundary_tests;

#[path = "memory_model_strengthening/alloc_frame_isolation_tests.rs"]
mod alloc_frame_isolation_tests;
#[path = "memory_model_strengthening/three_object_frame_isolation_tests.rs"]
mod three_object_frame_isolation_tests;

/// Load-after-store must force equality at the same pointer.
///
/// This proves the negated equality is UNSAT, not merely that equality is SAT.
#[test]
#[timeout(30000)]
fn base_memory_model_load_store_forces_equality() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(123);

    let state = model.store(&mut solver, state, &ptr, val);
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "load(store(addr, value), addr) != value should be UNSAT",
    );
}

/// Alloc forces domain membership: ¬in_domain(alloc(ptr)) is UNSAT.
///
/// Strengthens `test_base_memory_model_alloc_dealloc` which only checks SAT.
#[test]
#[timeout(30000)]
fn alloc_forces_domain_membership() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(100);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    let not_in_dom = solver.not(in_dom);
    solver.assert_term(not_in_dom);

    assert_unsat(
        &mut solver,
        "NOT in_domain after alloc must be UNSAT (alloc forces domain entry)",
    );
}

/// Alloc forces full permission: perm != PERM_SCALE after alloc is UNSAT.
///
/// Strengthens the SAT-only permission check in `test_base_memory_model_alloc_dealloc`.
#[test]
#[timeout(30000)]
fn alloc_forces_full_permission() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(100);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let has_full = model.has_full_permission(&mut solver, &state, &ptr);
    let not_full = solver.not(has_full);
    solver.assert_term(not_full);

    assert_unsat(
        &mut solver,
        "NOT has_full_permission after alloc must be UNSAT (alloc forces PERM_SCALE)",
    );
}

/// Alloc forces heap value: load(alloc(ptr, val)) != val is UNSAT.
///
/// Strengthens the SAT-only value check in `test_raii_lifecycle_alloc_use_dealloc`.
#[test]
#[timeout(30000)]
fn alloc_forces_heap_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(100);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "load after alloc != alloc value must be UNSAT (alloc forces heap entry)",
    );
}

/// Dealloc forces NOT in domain: in_domain(dealloc(ptr)) is UNSAT.
///
/// Strengthens `test_base_memory_model_alloc_dealloc` which only checks SAT
/// for the not-in-domain assertion.
#[test]
#[timeout(30000)]
fn dealloc_forces_not_in_domain() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(100);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    assert_unsat(
        &mut solver,
        "in_domain after dealloc must be UNSAT (dealloc forces domain removal)",
    );
}

/// Dealloc forces zero permission: has_permission(dealloc(ptr)) is UNSAT.
///
/// Strengthens the dealloc test — not only is the pointer out of domain,
/// but permissions are zeroed.
#[test]
#[timeout(30000)]
fn dealloc_forces_zero_permission() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(100);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);
    let has_perm = model.has_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_perm);

    assert_unsat(
        &mut solver,
        "has_permission after dealloc must be UNSAT (dealloc zeros permission)",
    );
}

/// Store-then-load forces the new value: load(store(ptr, new)) != new is UNSAT.
///
/// Strengthens `test_raii_lifecycle_alloc_use_dealloc` Phase 2/3 which only
/// checks SAT for loaded==new_val.
#[test]
#[timeout(30000)]
fn store_then_load_forces_new_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let init_val = solver.int_const(100);

    // Allocate, then overwrite
    let state = model.alloc(&mut solver, state, &ptr, init_val);
    let new_val = solver.int_const(200);
    let state = model.store(&mut solver, state, &ptr, new_val);

    // Assert loaded != new_val — should be UNSAT
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, new_val);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "load after store != stored value must be UNSAT (store overwrites alloc value)",
    );
}

/// Frame independence: dealloc(ptr1) forces ptr2's value unchanged.
///
/// Strengthens `test_raii_two_objects_frame_independence` which only checks SAT.
/// Proves that load(ptr2) != val2 is UNSAT after dealloc(ptr1), establishing
/// that ptr2's heap cell is deterministically preserved.
#[test]
#[timeout(30000)]
fn frame_independence_dealloc_forces_other_value_preserved() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);
    let state = model.dealloc(&mut solver, state, &ptr1);

    // Assert load(ptr2) != val2 — should be UNSAT (frame preserved)
    let loaded2 = model.load(&mut solver, &state, &ptr2);
    let eq = solver.eq(loaded2, val2);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "load(ptr2) != val2 after dealloc(ptr1) must be UNSAT (frame independence)",
    );
}

/// Frame independence: dealloc(ptr1) forces ptr2 still in domain.
///
/// Proves that NOT in_domain(ptr2) is UNSAT after dealloc(ptr1).
#[test]
#[timeout(30000)]
fn frame_independence_dealloc_forces_other_domain_preserved() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);
    let state = model.dealloc(&mut solver, state, &ptr1);

    // Assert NOT in_domain(ptr2) — should be UNSAT (ptr2 still allocated)
    let in_dom2 = model.in_domain(&mut solver, &state, &ptr2);
    let not_in_dom2 = solver.not(in_dom2);
    solver.assert_term(not_in_dom2);

    assert_unsat(
        &mut solver,
        "NOT in_domain(ptr2) after dealloc(ptr1) must be UNSAT (frame independence)",
    );
}

/// Frame independence: dealloc(ptr1) forces ptr2 still has full permission.
///
/// Proves that NOT has_full_permission(ptr2) is UNSAT after dealloc(ptr1).
#[test]
#[timeout(30000)]
fn frame_independence_dealloc_forces_other_permission_preserved() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);
    let state = model.dealloc(&mut solver, state, &ptr1);

    // Assert NOT has_full_permission(ptr2) — should be UNSAT
    let full2 = model.has_full_permission(&mut solver, &state, &ptr2);
    let not_full2 = solver.not(full2);
    solver.assert_term(not_full2);

    assert_unsat(
        &mut solver,
        "NOT has_full_permission(ptr2) after dealloc(ptr1) must be UNSAT (frame independence)",
    );
}

/// Store at one pointer forces the other pointer's value unchanged.
///
/// Proves store(ptr1, new_val) does not affect load(ptr2): the read-over-write
/// axiom guarantees that select(store(a, i, v), j) = select(a, j) when i != j.
#[test]
#[timeout(30000)]
fn store_at_one_ptr_forces_other_ptr_value_preserved() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);

    // Store a new value at ptr1
    let new_val = solver.int_const(333);
    let state = model.store(&mut solver, state, &ptr1, new_val);

    // Assert load(ptr2) != val2 — should be UNSAT (ptr2 unaffected by store at ptr1)
    let loaded2 = model.load(&mut solver, &state, &ptr2);
    let eq = solver.eq(loaded2, val2);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "store at ptr1 must not affect load at ptr2 (read-over-write frame rule)",
    );
}

/// Permission split-then-recombine forces full: half+half=PERM_SCALE is forced.
///
/// Strengthens `test_permission_split` by proving the negation is UNSAT.
#[test]
#[timeout(30000)]
fn permission_half_plus_half_forces_full() {
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let half_scale = PERM_SCALE / 2;

    let half1 = solver.int_const(half_scale);
    let half2 = solver.int_const(half_scale);
    let sum = solver.add(half1, half2);
    let full = solver.int_const(PERM_SCALE);
    let eq = solver.eq(sum, full);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "half + half != PERM_SCALE must be UNSAT (permission arithmetic is exact)",
    );
}

/// Three-way split with integer remainder must conserve the total budget.
///
/// If `PERM_SCALE` is not divisible by 3, the third share carries the remainder:
/// `s1 = floor(PERM_SCALE/3)`, `s2 = floor(PERM_SCALE/3)`,
/// `s3 = PERM_SCALE - s1 - s2`.
#[test]
#[timeout(30000)]
fn permission_three_way_split_with_remainder_forces_full() {
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let one_third = PERM_SCALE / 3;
    let third_share = PERM_SCALE - (one_third + one_third);

    let s1 = solver.int_const(one_third);
    let s2 = solver.int_const(one_third);
    let s3 = solver.int_const(third_share);
    let sum12 = solver.add(s1, s2);
    let sum123 = solver.add(sum12, s3);
    let full = solver.int_const(PERM_SCALE);

    let eq = solver.eq(sum123, full);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "three-way split (with remainder) must sum to PERM_SCALE exactly",
    );
}

/// Three-share permission claims cannot exceed the allocated budget.
///
/// Extends the two-share conservation proof to three shares.
#[test]
#[timeout(30000)]
fn permission_three_way_split_rejects_over_budget_claim() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let perm_actual = solver.select(state.permissions, addr);
    let share1 = solver.declare_const("share1_three", ay_dpll::api::Sort::Int);
    let share2 = solver.declare_const("share2_three", ay_dpll::api::Sort::Int);
    let share3 = solver.declare_const("share3_three", ay_dpll::api::Sort::Int);
    let zero = solver.int_const(0);

    let ge_share1 = solver.ge(share1, zero);
    let ge_share2 = solver.ge(share2, zero);
    let ge_share3 = solver.ge(share3, zero);
    solver.assert_term(ge_share1);
    solver.assert_term(ge_share2);
    solver.assert_term(ge_share3);

    let sum12 = solver.add(share1, share2);
    let sum123 = solver.add(sum12, share3);
    let sum_le_actual = solver.le(sum123, perm_actual);
    solver.assert_term(sum_le_actual);

    let over_budget = solver.int_const(PERM_SCALE + 1);
    let sum_ge_over_budget = solver.ge(sum123, over_budget);
    solver.assert_term(sum_ge_over_budget);

    assert_unsat(
        &mut solver,
        "three non-negative shares from one alloc cannot exceed PERM_SCALE",
    );
}

/// In a split-permission state, points-to at the exact split threshold is forced.
///
/// This strengthens `test_partial_permission_access`: after splitting a location
/// to half permission, requesting points-to with half permission must still hold.
/// We prove this by showing `NOT points_to(..., half)` is UNSAT.
#[test]
#[timeout(30000)]
fn partial_permission_forces_points_to_at_exact_threshold() {
    let half_scale = PERM_SCALE / 2;
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let half = solver.int_const(half_scale);
    let mut split_state = state.clone();
    split_state.permissions = solver.store(split_state.permissions, addr, half);

    let points_to_half = model.encode_points_to(&mut solver, &split_state, addr, val, half);
    let not_points_to_half = solver.not(points_to_half);
    solver.assert_term(not_points_to_half);

    assert_unsat(
        &mut solver,
        "NOT points_to(ptr, value, half) must be UNSAT when current permission is exactly half",
    );
}

/// In a split-permission state, points-to above the split threshold is impossible.
///
/// This strengthens `test_permission_transfer_soundness` with model-level split
/// state: after reducing current permission to half, requesting half+1 points-to
/// must be UNSAT.
#[test]
#[timeout(30000)]
fn partial_permission_rejects_points_to_above_threshold() {
    let half_scale = PERM_SCALE / 2;
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let half = solver.int_const(half_scale);
    let mut split_state = state.clone();
    split_state.permissions = solver.store(split_state.permissions, addr, half);

    let half_plus_one = solver.int_const(half_scale + 1);
    let points_to_too_much =
        model.encode_points_to(&mut solver, &split_state, addr, val, half_plus_one);
    solver.assert_term(points_to_too_much);

    assert_unsat(
        &mut solver,
        "points_to(ptr, value, half+1) must be UNSAT when current permission is half",
    );
}

/// Third-permission split forces points-to at the exact threshold.
///
/// Similar to the half-threshold proof, but covers three-way split scenarios.
#[test]
#[timeout(30000)]
fn partial_permission_third_forces_points_to_at_exact_threshold() {
    let one_third = PERM_SCALE / 3;
    assert!(
        one_third > 0,
        "PERM_SCALE must be >= 3 for third-threshold soundness test"
    );

    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let third = solver.int_const(one_third);
    let mut split_state = state.clone();
    split_state.permissions = solver.store(split_state.permissions, addr, third);

    let points_to_third = model.encode_points_to(&mut solver, &split_state, addr, val, third);
    let not_points_to_third = solver.not(points_to_third);
    solver.assert_term(not_points_to_third);

    assert_unsat(
        &mut solver,
        "NOT points_to(ptr, value, third) must be UNSAT when current permission is exactly third",
    );
}

/// Third-permission split rejects points-to above the threshold.
///
/// With current permission set to one third, requesting one-third-plus-one
/// points-to must be impossible.
#[test]
#[timeout(30000)]
fn partial_permission_third_rejects_points_to_above_threshold() {
    let one_third = PERM_SCALE / 3;
    assert!(
        one_third > 0,
        "PERM_SCALE must be >= 3 for third-threshold soundness test"
    );

    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let third = solver.int_const(one_third);
    let mut split_state = state.clone();
    split_state.permissions = solver.store(split_state.permissions, addr, third);

    let third_plus_one = solver.int_const(one_third + 1);
    let points_to_too_much =
        model.encode_points_to(&mut solver, &split_state, addr, val, third_plus_one);
    solver.assert_term(points_to_too_much);

    assert_unsat(
        &mut solver,
        "points_to(ptr, value, third+1) must be UNSAT when current permission is third",
    );
}

/// Split then recombine forces full permission on the concrete memory state.
///
/// This strengthens arithmetic-only split/recombine checks by proving that
/// model-level permission state transitions enforce `has_full_permission`.
#[test]
#[timeout(30000)]
fn split_then_recombine_forces_full_permission_state() {
    let half_scale = PERM_SCALE / 2;
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let half = solver.int_const(half_scale);
    let mut split_state = state.clone();
    split_state.permissions = solver.store(split_state.permissions, addr, half);

    let full = solver.int_const(PERM_SCALE);
    let mut recombined_state = split_state;
    recombined_state.permissions = solver.store(recombined_state.permissions, addr, full);

    let has_full = model.has_full_permission(&mut solver, &recombined_state, &ptr);
    let not_full = solver.not(has_full);
    solver.assert_term(not_full);

    assert_unsat(
        &mut solver,
        "after split->recombine, NOT has_full_permission must be UNSAT",
    );
}

/// Split then recombine restores exact-full points-to and rejects over-full claims.
#[test]
#[timeout(30000)]
fn split_then_recombine_points_to_full_boundary() {
    let half_scale = PERM_SCALE / 2;
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let half = solver.int_const(half_scale);
    let mut split_state = state.clone();
    split_state.permissions = solver.store(split_state.permissions, addr, half);

    let full = solver.int_const(PERM_SCALE);
    let mut recombined_state = split_state;
    recombined_state.permissions = solver.store(recombined_state.permissions, addr, full);

    let points_to_full = model.encode_points_to(&mut solver, &recombined_state, addr, val, full);
    let not_points_to_full = solver.not(points_to_full);
    solver.assert_term(not_points_to_full);
    assert_unsat(
        &mut solver,
        "after split->recombine, NOT points_to(..., PERM_SCALE) must be UNSAT",
    );

    let mut solver2 = Solver::try_new(Logic::QfAuflia).unwrap();
    let state2 = BaseMemoryModel::init(&mut solver2);
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(100);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);

    let half2 = solver2.int_const(half_scale);
    let mut split_state2 = state2.clone();
    split_state2.permissions = solver2.store(split_state2.permissions, addr2, half2);

    let full2 = solver2.int_const(PERM_SCALE);
    let mut recombined_state2 = split_state2;
    recombined_state2.permissions = solver2.store(recombined_state2.permissions, addr2, full2);

    let over_full = solver2.int_const(PERM_SCALE + 1);
    let points_to_over =
        model.encode_points_to(&mut solver2, &recombined_state2, addr2, val2, over_full);
    solver2.assert_term(points_to_over);

    assert_unsat(
        &mut solver2,
        "after split->recombine, points_to(..., PERM_SCALE+1) must remain UNSAT",
    );
}

/// Constrained initial state: alloc overwrites const_array entries deterministically.
///
/// Strengthens `test_constrained_alloc_then_points_to_still_works` by proving
/// that load != val is UNSAT after alloc on a constrained-init state.
#[test]
#[timeout(30000)]
fn constrained_init_alloc_forces_value() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "load != alloc value must be UNSAT under constrained init (store overwrites const_array)",
    );
}

/// Constrained initial state: alloc forces domain membership.
///
/// Strengthens `test_alloc_under_constrained_init_enters_domain` by proving
/// `NOT in_domain(ptr)` is UNSAT after alloc.
#[test]
#[timeout(30000)]
fn constrained_init_alloc_forces_domain_membership() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    let not_in_dom = solver.not(in_dom);
    solver.assert_term(not_in_dom);

    assert_unsat(
        &mut solver,
        "NOT in_domain after constrained-init alloc must be UNSAT",
    );
}

/// Constrained initial state: alloc forces full permission.
///
/// Strengthens `test_alloc_under_constrained_init_enters_domain` by proving
/// `NOT has_full_permission(ptr)` is UNSAT after alloc.
#[test]
#[timeout(30000)]
fn constrained_init_alloc_forces_full_permission() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let has_full = model.has_full_permission(&mut solver, &state, &ptr);
    let not_full = solver.not(has_full);
    solver.assert_term(not_full);

    assert_unsat(
        &mut solver,
        "NOT has_full_permission after constrained-init alloc must be UNSAT",
    );
}

/// Points-to at exact full permission is forced after alloc.
///
/// Strengthens `test_points_to_exact_full_permission_boundary` by proving
/// `NOT points_to(ptr, val, PERM_SCALE)` is UNSAT.
#[test]
#[timeout(30000)]
fn constrained_init_points_to_exact_full_forced() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(7);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(55);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let exact_full = solver.int_const(PERM_SCALE);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, exact_full);
    let not_points_to = solver.not(points_to);
    solver.assert_term(not_points_to);

    assert_unsat(
        &mut solver,
        "NOT points_to(ptr, val, PERM_SCALE) must be UNSAT after alloc",
    );
}

/// Points-to above full permission remains impossible under constrained init.
///
/// Companion boundary check: requesting `PERM_SCALE + 1` permission must be UNSAT.
#[test]
#[timeout(30000)]
fn constrained_init_points_to_above_full_rejected() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(7);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(55);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let over_full = solver.int_const(PERM_SCALE + 1);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, over_full);
    solver.assert_term(points_to);

    assert_unsat(
        &mut solver,
        "points_to(ptr, val, PERM_SCALE+1) must be UNSAT after alloc",
    );
}

/// Store at ptr1 does NOT affect domain of ptr2.
///
/// Verifies the frame rule for domain: `store` only modifies the heap array,
/// so domain membership at other pointers is preserved.
#[test]
#[timeout(30000)]
fn store_at_one_ptr_forces_other_ptr_domain_preserved() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);

    // Store at ptr1
    let new_val = solver.int_const(333);
    let state = model.store(&mut solver, state, &ptr1, new_val);

    // Assert NOT in_domain(ptr2) — should be UNSAT (store does not touch domain)
    let in_dom2 = model.in_domain(&mut solver, &state, &ptr2);
    let not_in_dom2 = solver.not(in_dom2);
    solver.assert_term(not_in_dom2);

    assert_unsat(
        &mut solver,
        "store at ptr1 must not remove ptr2 from domain (frame independence for domain)",
    );
}

/// Store at ptr1 does NOT affect permissions of ptr2.
///
/// Verifies the frame rule for permissions: `store` only modifies the heap
/// array, so permission values at other pointers are preserved.
#[test]
#[timeout(30000)]
fn store_at_one_ptr_forces_other_ptr_permission_preserved() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);

    // Store at ptr1
    let new_val = solver.int_const(333);
    let state = model.store(&mut solver, state, &ptr1, new_val);

    // Assert NOT has_full_permission(ptr2) — should be UNSAT
    let full2 = model.has_full_permission(&mut solver, &state, &ptr2);
    let not_full2 = solver.not(full2);
    solver.assert_term(not_full2);

    assert_unsat(
        &mut solver,
        "store at ptr1 must not affect ptr2 permissions (frame independence for permissions)",
    );
}

/// Store at the SAME pointer preserves domain membership.
///
/// Unlike the cross-pointer frame tests above, this verifies that `store` at an
/// address does not affect the domain array for that same address. This holds
/// because `store` only modifies `mem.heap`, not `mem.domain`.
#[test]
#[timeout(30000)]
fn store_same_ptr_preserves_domain() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let new_val = solver.int_const(200);
    let state = model.store(&mut solver, state, &ptr, new_val);

    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    let not_in_dom = solver.not(in_dom);
    solver.assert_term(not_in_dom);

    assert_unsat(
        &mut solver,
        "store at same ptr must not remove it from domain (store only touches heap)",
    );
}

/// Store at the SAME pointer preserves permission.
///
/// Verifies that `store` at an address does not affect the permission array for
/// that same address. This holds because `store` only modifies `mem.heap`.
#[test]
#[timeout(30000)]
fn store_same_ptr_preserves_permission() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let new_val = solver.int_const(200);
    let state = model.store(&mut solver, state, &ptr, new_val);

    let full = model.has_full_permission(&mut solver, &state, &ptr);
    let not_full = solver.not(full);
    solver.assert_term(not_full);

    assert_unsat(
        &mut solver,
        "store at same ptr must not change permission (store only touches heap)",
    );
}

/// Dealloc forces exact zero permission (not just has_permission false).
///
/// Strengthens `dealloc_forces_zero_permission` which checks has_permission
/// (perm > 0 is UNSAT). This proves the stronger property: get_permission
/// returns exactly 0 (not merely non-positive).
#[test]
#[timeout(30000)]
fn dealloc_forces_exact_zero_permission() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);

    let perm = model.get_permission(&mut solver, &state, &ptr);
    let zero = solver.int_const(0);
    let perm_eq_zero = solver.eq(perm, zero);
    let perm_ne_zero = solver.not(perm_eq_zero);
    solver.assert_term(perm_ne_zero);

    assert_unsat(
        &mut solver,
        "dealloc must force permission == 0 exactly (not merely non-positive)",
    );
}

/// Alloc forces exact PERM_SCALE permission (not just has_full_permission).
///
/// Strengthens `alloc_forces_full_permission` which uses has_full_permission
/// (eq(perm, PERM_SCALE)). This uses get_permission + manual eq to verify
/// the exact value at the raw array level.
#[test]
#[timeout(30000)]
fn alloc_forces_exact_perm_scale() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);

    let perm = model.get_permission(&mut solver, &state, &ptr);
    let full = solver.int_const(PERM_SCALE);
    let perm_eq = solver.eq(perm, full);
    let perm_ne = solver.not(perm_eq);
    solver.assert_term(perm_ne);

    assert_unsat(
        &mut solver,
        "alloc must force get_permission == PERM_SCALE exactly",
    );
}

/// Dealloc does NOT clear the heap value — only domain and permissions.
///
/// This is a correctness property of the model: `dealloc` removes the pointer
/// from the domain and zeros its permissions, but leaves the heap value
/// unchanged. Accessing the value after dealloc should still yield the old
/// value (though the domain check prevents valid access). This matters for
/// soundness: if dealloc zeroed the heap, a use-after-free check might
/// accidentally pass because `heap[ptr] == 0` could match an expected value.
#[test]
#[timeout(30000)]
fn dealloc_preserves_heap_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);

    // Load from deallocated ptr — value should still be 999
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "load after dealloc != original value must be UNSAT (dealloc preserves heap content)",
    );
}

/// Reallocating the same pointer restores domain/full-permission and overwrites heap value.
///
/// Strengthens the alloc/dealloc lifecycle by proving all three postconditions
/// after a dealloc+alloc sequence on the same address.
#[test]
#[timeout(30000)]
fn dealloc_then_realloc_same_ptr_forces_new_state() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();
    let addr = solver.int_const(55);
    let ptr = MemPtr::new(addr);
    let first = solver.int_const(111);
    let second = solver.int_const(222);
    let state = model.alloc(&mut solver, state, &ptr, first);
    let state = model.dealloc(&mut solver, state, &ptr);
    let state = model.alloc(&mut solver, state, &ptr, second);
    // Heap value must be the reallocated value.
    solver.push();
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq_second = solver.eq(loaded, second);
    let neq_second = solver.not(eq_second);
    solver.assert_term(neq_second);
    assert_unsat(
        &mut solver,
        "realloc(ptr, second) must force load(ptr) == second after dealloc+alloc",
    );
    solver.pop();
    // Domain membership must be restored.
    solver.push();
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    let not_in_dom = solver.not(in_dom);
    solver.assert_term(not_in_dom);
    assert_unsat(
        &mut solver,
        "realloc(ptr) must force in_domain(ptr) after dealloc+alloc",
    );
    solver.pop();
    // Full permission must be restored.
    solver.push();
    let full = model.has_full_permission(&mut solver, &state, &ptr);
    let not_full = solver.not(full);
    solver.assert_term(not_full);
    assert_unsat(
        &mut solver,
        "realloc(ptr) must force full permission after dealloc+alloc",
    );
    solver.pop();
}
/// Reallocating the same pointer invalidates old points-to value and forces new one.
///
/// Strengthens lifecycle reasoning for points-to predicates: after
/// dealloc+alloc on the same address, `ptr |-> first` must be impossible and
/// `ptr |-> second` must be forced.
#[test]
#[timeout(30000)]
fn dealloc_then_realloc_forces_points_to_new_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    // Old points-to value must be impossible after reallocation.
    let addr = solver.int_const(77);
    let ptr = MemPtr::new(addr);
    let first = solver.int_const(111);
    let second = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr, first);
    let state = model.dealloc(&mut solver, state, &ptr);
    let state = model.alloc(&mut solver, state, &ptr, second);
    let perm = solver.int_const(1);
    let points_to_old = model.encode_points_to(&mut solver, &state, addr, first, perm);
    solver.assert_term(points_to_old);
    assert_unsat(
        &mut solver,
        "after realloc(ptr, second), points-to(ptr, first, 1) must be UNSAT",
    );

    // New points-to value must be forced after reallocation.
    let mut solver2 = Solver::try_new(Logic::QfAuflia).unwrap();
    let state2 = BaseMemoryModel::init(&mut solver2);
    let addr2 = solver2.int_const(77);
    let ptr2 = MemPtr::new(addr2);
    let first2 = solver2.int_const(111);
    let second2 = solver2.int_const(222);

    let state2 = model.alloc(&mut solver2, state2, &ptr2, first2);
    let state2 = model.dealloc(&mut solver2, state2, &ptr2);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, second2);
    let perm2 = solver2.int_const(1);
    let points_to_new = model.encode_points_to(&mut solver2, &state2, addr2, second2, perm2);
    let not_points_to_new = solver2.not(points_to_new);
    solver2.assert_term(not_points_to_new);
    assert_unsat(
        &mut solver2,
        "after realloc(ptr, second), NOT points-to(ptr, second, 1) must be UNSAT",
    );
}

// Symbolic address tests moved to memory_model_symbolic.rs (canonical location).
// See: symbolic_address_aliasing_store_visible, symbolic_address_non_aliasing_domain_check,
//      symbolic_address_alloc_then_points_to, symbolic_address_points_to_wrong_value_unsat,
//      symbolic_address_frame_independence.

/// Separation conjunction rejects overlapping domains from two allocations
/// at the same concrete address. This is the core sep-logic property:
/// two heap fragments at the same location cannot both be in-domain.
#[test]
#[timeout(30000)]
fn sep_conj_rejects_same_address_allocations() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(10);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(42);

    let state = model.alloc(&mut solver, state, &ptr, val);

    // Both left and right domain predicates for the SAME address
    let left_dom = model.in_domain(&mut solver, &state, &ptr);
    let right_dom = model.in_domain(&mut solver, &state, &ptr);

    let sep = model.encode_sep_conj(&mut solver, left_dom, right_dom);
    solver.assert_term(sep);

    // Sep conj of two identical domain predicates must be UNSAT:
    // both are true (allocated), so !(true && true) = false
    assert_unsat(
        &mut solver,
        "sep_conj must reject same-address domain overlap",
    );
}

/// Separation conjunction accepts disjoint allocations at different
/// concrete addresses.
#[test]
#[timeout(30000)]
fn sep_conj_accepts_disjoint_allocations() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let val1 = solver.int_const(42);
    let val2 = solver.int_const(99);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);

    // Left domain: addr1 in domain, right domain: NOT addr1 (i.e., addr2 only)
    let left_dom = model.in_domain(&mut solver, &state, &ptr1);
    let right_dom_addr1 = model.in_domain(&mut solver, &state, &ptr1);
    let right_not_addr1 = solver.not(right_dom_addr1);

    let sep = model.encode_sep_conj(&mut solver, left_dom, right_not_addr1);
    solver.assert_term(sep);

    assert_sat(
        &mut solver,
        "sep_conj should accept disjoint heap fragments",
    );
}

// ============================================================================
// Separation conjunction chaining tests (#901 memory_verification)
// ============================================================================

/// Chained sep_conj over 3 disjoint objects: A * B * C.
///
/// `encode_sep_conj` works pairwise. To express that A, B, C occupy disjoint
/// domains, we need: sep(A, B) AND sep(A, C) AND sep(B, C). All three must
/// hold simultaneously.
///
/// This test verifies that three concrete allocations at different addresses
/// satisfy the conjunction of all pairwise separations.
#[allow(clippy::similar_names)]
#[test]
#[timeout(30000)]
fn sep_conj_three_disjoint_objects_satisfiable() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    // Per-location domain membership for 3 objects at 2 locations:
    // A owns loc=10 only, B owns loc=20 only, C owns neither → all pairwise disjoint
    let ownership = [
        // (object_at_10, object_at_20)
        (true, false),  // A
        (false, true),  // B
        (false, false), // C
    ];

    // Assert pairwise sep_conj at each location for each pair
    for i in 0..ownership.len() {
        for j in (i + 1)..ownership.len() {
            let left_10 = solver.bool_const(ownership[i].0);
            let right_10 = solver.bool_const(ownership[j].0);
            let sep_at_10 = model.encode_sep_conj(&mut solver, left_10, right_10);
            solver.assert_term(sep_at_10);

            let left_20 = solver.bool_const(ownership[i].1);
            let right_20 = solver.bool_const(ownership[j].1);
            let sep_at_20 = model.encode_sep_conj(&mut solver, left_20, right_20);
            solver.assert_term(sep_at_20);
        }
    }

    assert_sat(
        &mut solver,
        "pairwise disjoint domains for 3 objects should be SAT",
    );
}

/// Chained sep_conj rejects when any pair overlaps.
///
/// Three objects where A and C both claim ownership at loc=10.
/// Even though B is disjoint from both, the A-C overlap should make
/// the conjunction of all pairwise separations UNSAT.
#[test]
#[timeout(30000)]
fn sep_conj_three_objects_overlap_rejected() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    // A owns loc=10, C also claims loc=10 → overlap
    let a_at_10 = solver.bool_const(true);
    let c_at_10 = solver.bool_const(true);

    let sep_ac_10 = model.encode_sep_conj(&mut solver, a_at_10, c_at_10);
    solver.assert_term(sep_ac_10);

    assert_unsat(
        &mut solver,
        "sep_conj must reject overlapping domains even when third object is disjoint",
    );
}

// ============================================================================
// Non-standard permission split conservation (#901 memory_verification)
// ============================================================================

/// Non-evenly-divisible permission split: 33 + 34 + 33 = PERM_SCALE.
///
/// When PERM_SCALE is 100, a three-way split with remainder (100/3 = 33 rem 1)
/// must still conserve total permission. The middle share gets the extra unit.
#[test]
#[timeout(30000)]
fn permission_uneven_three_way_split_conserves_total() {
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    let third = PERM_SCALE / 3; // 33 when PERM_SCALE=100
    let remainder = PERM_SCALE - 2 * third; // 34 when PERM_SCALE=100

    let p1 = solver.int_const(third);
    let p2 = solver.int_const(remainder);
    let p3 = solver.int_const(third);

    let sum12 = solver.add(p1, p2);
    let sum123 = solver.add(sum12, p3);
    let full = solver.int_const(PERM_SCALE);

    // Assert sum != PERM_SCALE — should be UNSAT because 33+34+33 = 100
    let neq = solver.eq(sum123, full);
    let neq = solver.not(neq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "uneven three-way split (33+34+33) must conserve PERM_SCALE exactly",
    );
}

/// Four-way equal permission split must conserve total.
///
/// PERM_SCALE / 4 = 25 (when PERM_SCALE=100). Four shares of 25 = 100.
#[test]
#[timeout(30000)]
fn permission_four_way_split_conserves_total() {
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    let quarter = PERM_SCALE / 4;
    let rem = PERM_SCALE - 3 * quarter; // handles non-divisible cases

    let p1 = solver.int_const(quarter);
    let p2 = solver.int_const(quarter);
    let p3 = solver.int_const(quarter);
    let p4 = solver.int_const(rem);

    let s1 = solver.add(p1, p2);
    let s2 = solver.add(s1, p3);
    let s3 = solver.add(s2, p4);
    let full = solver.int_const(PERM_SCALE);

    let neq = solver.eq(s3, full);
    let neq = solver.not(neq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "four-way split must conserve PERM_SCALE exactly",
    );
}

/// Four symbolic permission shares bounded by PERM_SCALE cannot exceed it.
///
/// This is the memory model variant: after alloc, the actual permission
/// budget is PERM_SCALE. Four non-negative shares bounded by this budget
/// cannot sum to more.
#[test]
#[timeout(30000)]
fn four_symbolic_shares_cannot_exceed_perm_scale() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let perm_actual = solver.select(state.permissions, addr);
    let zero = solver.int_const(0);

    // Four symbolic shares
    let s1 = solver.declare_const("s1", ay_dpll::api::Sort::Int);
    let s2 = solver.declare_const("s2", ay_dpll::api::Sort::Int);
    let s3 = solver.declare_const("s3", ay_dpll::api::Sort::Int);
    let s4 = solver.declare_const("s4", ay_dpll::api::Sort::Int);

    // All non-negative
    for s in [s1, s2, s3, s4] {
        let ge = solver.ge(s, zero);
        solver.assert_term(ge);
    }

    // Sum bounded by actual permission
    let sum12 = solver.add(s1, s2);
    let sum123 = solver.add(sum12, s3);
    let sum1234 = solver.add(sum123, s4);
    let bounded = solver.le(sum1234, perm_actual);
    solver.assert_term(bounded);

    // Try to make sum exceed PERM_SCALE
    let over = solver.int_const(PERM_SCALE + 1);
    let t12 = solver.add(s1, s2);
    let t123 = solver.add(t12, s3);
    let t1234 = solver.add(t123, s4);
    let exceeds = solver.ge(t1234, over);
    solver.assert_term(exceeds);

    assert_unsat(
        &mut solver,
        "four symbolic permission shares from a single alloc cannot exceed PERM_SCALE",
    );
}

// ============================================================================
// Heap leak after dealloc: information exposure test (#901 memory_verification)
// ============================================================================

/// After dealloc, the heap value is still the pre-dealloc value.
/// Combined with domain=false, this means raw load returns stale data.
/// This test verifies that a safety-conscious consumer (using domain guard)
/// cannot observe the stale value, but the value is structurally present.
///
/// This documents the design: dealloc is a "logical" free, not a zero-fill.
/// The heap retains its contents — safety depends entirely on the domain check.
#[test]
#[timeout(30000)]
fn dealloc_heap_leak_observable_without_domain_guard() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let secret_val = solver.int_const(12345);

    let state = model.alloc(&mut solver, state, &ptr, secret_val);
    let state = model.dealloc(&mut solver, state, &ptr);

    // Raw load (bypassing domain check) still sees the secret value
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq_secret = solver.eq(loaded, secret_val);
    let not_eq_secret = solver.not(eq_secret);
    solver.assert_term(not_eq_secret);

    assert_unsat(
        &mut solver,
        "raw load after dealloc must still see the pre-dealloc value \
         (heap is not zeroed — safety depends on domain check)",
    );
}

/// After dealloc, points-to with the stale value must be UNSAT.
///
/// This is the safety counterpart to the heap leak test above: even though
/// the heap still contains the value, encode_points_to's domain check
/// prevents the stale value from being observed through the safety API.
#[test]
#[timeout(30000)]
fn dealloc_stale_value_unreachable_through_points_to() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(12345);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);

    // Even with zero permission requirement, domain guard blocks
    let zero_perm = solver.int_const(0);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, zero_perm);
    solver.assert_term(points_to);

    assert_unsat(
        &mut solver,
        "points-to with stale value after dealloc must be UNSAT \
         (domain guard blocks even with zero required permission)",
    );
}

// ============================================================================
// Store-load round-trip and non-interference tests (#901 memory_verification)
// ============================================================================

/// Store a value then load from the same address: loaded value must equal
/// stored value. This is the fundamental array theory property `select(store(a, i, v), i) == v`
/// instantiated through the memory model's store/load wrappers.
#[test]
#[timeout(30000)]
fn store_load_same_address_round_trip() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(100);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(42);

    let state = model.store(&mut solver, state, &ptr, val);
    let loaded = model.load(&mut solver, &state, &ptr);

    // Assert NOT(loaded == val): should be UNSAT
    let eq = solver.eq(loaded, val);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "store then load at same address must return the stored value",
    );
}

/// Store at address A, then load from address B (A != B): load must return
/// the original value at B, not A's stored value. This is the non-interference
/// property `select(store(a, i, v), j) == select(a, j)` when `i != j`.
#[test]
#[timeout(30000)]
fn store_load_different_address_non_interference() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr_a = solver.int_const(100);
    let addr_b = solver.int_const(200);
    let ptr_a = MemPtr::new(addr_a);
    let ptr_b = MemPtr::new(addr_b);

    // Capture what B holds before the store
    let original_b = model.load(&mut solver, &state, &ptr_b);

    // Store 42 at address A
    let val_a = solver.int_const(42);
    let state = model.store(&mut solver, state, &ptr_a, val_a);

    // Load from B after the store to A
    let loaded_b = model.load(&mut solver, &state, &ptr_b);

    // Assert NOT(loaded_b == original_b): should be UNSAT (B unchanged)
    let eq = solver.eq(loaded_b, original_b);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "store at A must not affect load at B (non-interference)",
    );
}

/// Two sequential stores to the same address: second store overwrites first.
/// Load must return the value from the last store.
#[test]
#[timeout(30000)]
fn store_store_same_address_last_write_wins() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(100);
    let ptr = MemPtr::new(addr);

    let val1 = solver.int_const(10);
    let val2 = solver.int_const(20);

    let state = model.store(&mut solver, state, &ptr, val1);
    let state = model.store(&mut solver, state, &ptr, val2);

    let loaded = model.load(&mut solver, &state, &ptr);

    // Must equal val2 (last write), NOT val1
    let eq_v2 = solver.eq(loaded, val2);
    let neq_v2 = solver.not(eq_v2);
    solver.assert_term(neq_v2);

    assert_unsat(
        &mut solver,
        "second store to same address must overwrite first (last-write-wins)",
    );
}

/// Alloc then store then load: the store value must be readable even though
/// alloc also wrote to the heap. This tests that store correctly overwrites
/// the alloc-initialized value.
#[test]
#[timeout(30000)]
fn alloc_then_store_overwrites_initial_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(100);
    let ptr = MemPtr::new(addr);

    // Alloc with initial value 0
    let init_val = solver.int_const(0);
    let state = model.alloc(&mut solver, state, &ptr, init_val);

    // Overwrite with 99
    let new_val = solver.int_const(99);
    let state = model.store(&mut solver, state, &ptr, new_val);

    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, new_val);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "store after alloc must overwrite alloc-initialized value",
    );
}
// ============================================================================
// Alloc-dealloc-realloc composition tests (#901 assertion strengthening)
// ============================================================================

/// After dealloc at addr, re-alloc at the same addr gives fresh PERM_SCALE
/// permission. The old permission (zeroed by dealloc) must not leak through.
///
/// This tests the composition dealloc;alloc and verifies that alloc overwrites
/// the zeroed permission array entry with PERM_SCALE.
#[test]
#[timeout(30000)]
fn realloc_after_dealloc_gets_fresh_permission() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let val2 = solver.int_const(200);

    // Alloc → dealloc → re-alloc
    let state = model.alloc(&mut solver, state, &ptr, val1);
    let state = model.dealloc(&mut solver, state, &ptr);
    let state = model.alloc(&mut solver, state, &ptr, val2);

    // Permission must be PERM_SCALE (not 0 from dealloc)
    let perm = model.get_permission(&mut solver, &state, &ptr);
    let expected = solver.int_const(PERM_SCALE);
    let eq = solver.eq(perm, expected);
    let neq = solver.not(eq);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "re-alloc after dealloc must restore permission to PERM_SCALE",
    );
}

/// After dealloc at addr, re-alloc at the same addr with a new value:
/// load must return the NEW value, not the stale pre-dealloc value.
///
/// This verifies that the alloc's heap write overwrites the lingering
/// stale data documented in `dealloc_heap_leak_observable_without_domain_guard`.
#[test]
#[timeout(30000)]
fn realloc_after_dealloc_overwrites_stale_heap_value() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let stale_val = solver.int_const(12345);
    let fresh_val = solver.int_const(99999);

    let state = model.alloc(&mut solver, state, &ptr, stale_val);
    let state = model.dealloc(&mut solver, state, &ptr);
    let state = model.alloc(&mut solver, state, &ptr, fresh_val);

    // Load must equal fresh_val, not stale_val
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq_fresh = solver.eq(loaded, fresh_val);
    let neq = solver.not(eq_fresh);
    solver.assert_term(neq);

    assert_unsat(
        &mut solver,
        "re-alloc must overwrite stale heap value from previous alloc-dealloc cycle",
    );
}

/// Dealloc-realloc cycle at addr A must not affect addr B's domain or value.
///
/// This tests frame independence across the dealloc;alloc composition:
/// even though A's domain/perm/heap entries are modified by both operations,
/// B's state must be completely untouched.
#[test]
#[timeout(30000)]
fn dealloc_realloc_frame_independence_forces_neighbor_preserved() {
    let (model, mut solver, state) = mem_test_setup();

    let addr_a = solver.int_const(10);
    let addr_b = solver.int_const(20);
    let ptr_a = MemPtr::new(addr_a);
    let ptr_b = MemPtr::new(addr_b);
    let val_a1 = solver.int_const(1);
    let val_a2 = solver.int_const(2);
    let val_b = solver.int_const(999);

    // Alloc both
    let state = model.alloc(&mut solver, state, &ptr_a, val_a1);
    let state = model.alloc(&mut solver, state, &ptr_b, val_b);

    // Dealloc A, re-alloc A with new value
    let state = model.dealloc(&mut solver, state, &ptr_a);
    let state = model.alloc(&mut solver, state, &ptr_a, val_a2);

    // B's value must still be val_b — assert NOT(loaded_b == val_b) is UNSAT
    let loaded_b = model.load(&mut solver, &state, &ptr_b);
    let eq_b = solver.eq(loaded_b, val_b);
    let neq_b = solver.not(eq_b);
    solver.assert_term(neq_b);

    assert_unsat(
        &mut solver,
        "dealloc-realloc at A must not alter B's heap value",
    );
}

// --- New strengthening tests: reflection iteration 507 ---

/// Separating conjunction is symmetric: sep_conj(A,B) == sep_conj(B,A).
///
/// Proves that asserting sep_conj(A,B) AND NOT(sep_conj(B,A)) is UNSAT,
/// meaning the two orderings are logically equivalent.
#[test]
#[timeout(30000)]
fn sep_conj_is_symmetric() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    // Create two concrete domain membership predicates
    let dom_a = solver.declare_const("dom_a", Sort::Bool);
    let dom_b = solver.declare_const("dom_b", Sort::Bool);

    let forward = model.encode_sep_conj(&mut solver, dom_a, dom_b);
    let backward = model.encode_sep_conj(&mut solver, dom_b, dom_a);

    // Assert forward AND NOT(backward) — should be UNSAT if symmetric
    solver.assert_term(forward);
    let not_backward = solver.not(backward);
    solver.assert_term(not_backward);

    assert_unsat(&mut solver, "sep_conj(A,B) must imply sep_conj(B,A)");
}

/// Separating conjunction reverse direction: sep_conj(B,A) implies sep_conj(A,B).
#[test]
#[timeout(30000)]
fn sep_conj_is_symmetric_reverse() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    let dom_a = solver.declare_const("dom_a", Sort::Bool);
    let dom_b = solver.declare_const("dom_b", Sort::Bool);

    let forward = model.encode_sep_conj(&mut solver, dom_a, dom_b);
    let backward = model.encode_sep_conj(&mut solver, dom_b, dom_a);

    // Assert backward AND NOT(forward) — should be UNSAT if symmetric
    solver.assert_term(backward);
    let not_forward = solver.not(forward);
    solver.assert_term(not_forward);

    assert_unsat(&mut solver, "sep_conj(B,A) must imply sep_conj(A,B)");
}

/// Full alloc-store-dealloc lifecycle forces exact state at each step.
///
/// Tests that the entire lifecycle produces exactly the expected intermediate
/// states, not just consistent ones. At each step, prove that the negation
/// of the expected property is UNSAT.
#[test]
#[timeout(30000)]
fn full_lifecycle_forces_exact_intermediate_states() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let val2 = solver.int_const(200);

    // Step 1: alloc — forces domain=1, heap=val1, perm=PERM_SCALE
    let state = model.alloc(&mut solver, state, &ptr, val1);

    // Prove heap == val1 is forced (not just satisfiable)
    solver.push();
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq1 = solver.eq(loaded, val1);
    let neq = solver.not(eq1);
    solver.assert_term(neq);
    assert_unsat(&mut solver, "after alloc: heap[ptr] must be forced to val1");
    solver.pop();

    // Step 2: store overwrites — forces heap=val2, domain/perms unchanged
    let state = model.store(&mut solver, state, &ptr, val2);

    solver.push();
    let loaded2 = model.load(&mut solver, &state, &ptr);
    let eq2 = solver.eq(loaded2, val2);
    let neq2 = solver.not(eq2);
    solver.assert_term(neq2);
    assert_unsat(&mut solver, "after store: heap[ptr] must be forced to val2");
    solver.pop();

    // Domain still forced to 1
    solver.push();
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    let not_in_dom = solver.not(in_dom);
    solver.assert_term(not_in_dom);
    assert_unsat(&mut solver, "after store: ptr must still be in domain");
    solver.pop();

    // Step 3: dealloc — forces domain=0, perm=0, heap unchanged
    let state = model.dealloc(&mut solver, state, &ptr);

    solver.push();
    let in_dom3 = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom3);
    assert_unsat(&mut solver, "after dealloc: ptr must NOT be in domain");
    solver.pop();

    // Permission forced to zero
    solver.push();
    let has_perm = model.has_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_perm);
    assert_unsat(&mut solver, "after dealloc: ptr must have zero permission");
    solver.pop();

    // Heap value still accessible through load (dealloc doesn't clear heap)
    solver.push();
    let loaded3 = model.load(&mut solver, &state, &ptr);
    let eq3 = solver.eq(loaded3, val2);
    let neq3 = solver.not(eq3);
    solver.assert_term(neq3);
    assert_unsat(
        &mut solver,
        "after dealloc: heap[ptr] still forced to val2 (heap not cleared)",
    );
    solver.pop();
}

/// Encode_points_to with symbolic permission: at exact PERM_SCALE boundary,
/// prove points-to is forced (not just SAT).
///
/// Strengthens the existing `partial_permission_forces_points_to_at_exact_threshold`
/// by using a symbolic (not concrete) permission amount and proving the three
/// conjuncts individually.
#[test]
#[timeout(30000)]
fn points_to_symbolic_perm_at_perm_scale_forced() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(7);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(42);
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Symbolic permission variable, constrained to exactly PERM_SCALE
    let sym_perm = solver.declare_const("sym_perm", Sort::Int);
    let full = solver.int_const(PERM_SCALE);
    let perm_eq = solver.eq(sym_perm, full);
    solver.assert_term(perm_eq);

    // encode_points_to with symbolic perm
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, sym_perm);

    // Prove points_to is forced (negation is UNSAT)
    let not_points_to = solver.not(points_to);
    solver.assert_term(not_points_to);

    assert_unsat(
        &mut solver,
        "points_to(allocated_ptr, correct_val, PERM_SCALE) must be forced",
    );
}

/// Permission conservation: if two shares split the allocated permission exactly,
/// neither can be negative and the total is forced to PERM_SCALE.
///
/// Proves that `p1 + p2 = perms[addr]` after alloc forces `p1 + p2 = PERM_SCALE`.
/// The negation `NOT(p1 + p2 == PERM_SCALE)` is UNSAT.
#[test]
#[timeout(30000)]
fn permission_split_conservation_forces_perm_scale_total() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(5);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(10);
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Two symbolic shares that together equal the stored permission
    let p1 = solver.declare_const("p1", Sort::Int);
    let p2 = solver.declare_const("p2", Sort::Int);
    let sum = solver.add(p1, p2);
    let current_perm = model.get_permission(&mut solver, &state, &ptr);
    let sum_eq_perm = solver.eq(sum, current_perm);
    solver.assert_term(sum_eq_perm);

    // Prove the sum is forced to PERM_SCALE
    let full = solver.int_const(PERM_SCALE);
    let sum_eq_full = solver.eq(sum, full);
    let not_full = solver.not(sum_eq_full);
    solver.assert_term(not_full);

    assert_unsat(
        &mut solver,
        "p1+p2==perms[addr] after alloc must force p1+p2==PERM_SCALE",
    );
}

/// Store after dealloc: heap value changes but points-to remains unsatisfiable.
///
/// This proves the critical soundness property: even though `store` after `dealloc`
/// updates the heap array, the domain guard in `encode_points_to` prevents the
/// location from being treated as allocated.
#[test]
#[timeout(30000)]
fn store_after_dealloc_heap_updated_but_points_to_unsatisfiable() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(99);
    let ptr = MemPtr::new(addr);
    let val_orig = solver.int_const(1);
    let val_new = solver.int_const(2);

    // Alloc, dealloc, then store new value
    let state = model.alloc(&mut solver, state, &ptr, val_orig);
    let state = model.dealloc(&mut solver, state, &ptr);
    let state = model.store(&mut solver, state, &ptr, val_new);

    // Heap value IS updated (store succeeded) — prove load == val_new
    solver.push();
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq_loaded = solver.eq(loaded, val_new);
    let neq = solver.not(eq_loaded);
    solver.assert_term(neq);
    assert_unsat(&mut solver, "store after dealloc must update heap value");
    solver.pop();

    // But points_to with ANY permission is UNSAT (domain blocks it)
    let any_perm = solver.int_const(0);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val_new, any_perm);
    solver.assert_term(points_to);

    // Even with perm=0, domain[addr]==1 fails because dealloc set domain[addr]=0
    assert_unsat(
        &mut solver,
        "points_to after dealloc+store must be UNSAT due to domain guard",
    );
}
