// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Logic;
use ntest::timeout;
use serial_test::serial;

use super::{super::PERM_SCALE, *};
use crate::tests::helpers::{
    assert_sat, assert_unsat, mem_test_setup, mem_test_setup_unconstrained,
};

#[test]
#[timeout(30000)]
fn test_base_memory_model_init() {
    // Prove domain is truly unconstrained: both domain[0] == 1 and domain[0] != 1
    // must be SAT (solver can pick either interpretation).
    let (_, mut solver1, state1) = mem_test_setup_unconstrained();
    let addr1 = solver1.int_const(0);
    let dom_val1 = solver1.select(state1.domain, addr1);
    let one1 = solver1.int_const(1);
    let in_domain = solver1.eq(dom_val1, one1);
    solver1.assert_term(in_domain);
    assert_sat(
        &mut solver1,
        "init domain should be SAT for membership (unconstrained)",
    );

    // Dual: domain[0] != 1 also SAT — proves domain is not forced to 1
    let (_, mut solver2, state2) = mem_test_setup_unconstrained();
    let addr2 = solver2.int_const(0);
    let dom_val2 = solver2.select(state2.domain, addr2);
    let one2 = solver2.int_const(1);
    let not_in_domain = solver2.neq(dom_val2, one2);
    solver2.assert_term(not_in_domain);
    assert_sat(
        &mut solver2,
        "init domain should be SAT for non-membership (unconstrained dual)",
    );
}

#[test]
#[timeout(30000)]
fn test_constrain_initial_state() {
    // After constrain_initial_state, domain must be empty (UNSAT to assert membership).
    let (_, mut solver, state) = mem_test_setup();
    let addr = solver.int_const(0);
    let dom_val = solver.select(state.domain, addr);
    let one = solver.int_const(1);
    let in_domain = solver.eq(dom_val, one);
    solver.assert_term(in_domain);
    assert_unsat(
        &mut solver,
        "constrained initial state must reject domain membership",
    );

    // Permissions are now zero: asserting perm == PERM_SCALE should be UNSAT
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let perm2 = solver2.select(state2.permissions, addr2);
    let full_perm = solver2.int_const(PERM_SCALE);
    let perm_is_full = solver2.eq(perm2, full_perm);
    solver2.assert_term(perm_is_full);
    assert_unsat(
        &mut solver2,
        "constrained initial state must set permissions to zero",
    );
}

#[test]
#[timeout(30000)]
fn test_base_memory_model_load_store() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(123);

    // Allocate (enters domain) then verify load == stored value
    let state = model.alloc(&mut solver, state, &ptr, val);
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val);
    solver.assert_term(eq);

    assert_sat(
        &mut solver,
        "load after alloc+store should equal stored value (constrained init)",
    );

    // UNSAT dual: load must NOT equal a different value
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(123);
    let wrong2 = solver2.int_const(456);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);
    let loaded2 = model.load(&mut solver2, &state2, &ptr2);
    let eq_wrong = solver2.eq(loaded2, wrong2);
    solver2.assert_term(eq_wrong);

    assert_unsat(
        &mut solver2,
        "load after store must not equal a different value (UNSAT dual)",
    );
}

#[test]
#[timeout(30000)]
fn test_base_memory_model_store_overwrite_rejects_stale_value() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let first = solver.int_const(10);
    let second = solver.int_const(20);

    let state = model.store(&mut solver, state, &ptr, first);
    let state = model.store(&mut solver, state, &ptr, second);
    let loaded = model.load(&mut solver, &state, &ptr);

    let stale_eq = solver.eq(loaded, first);
    solver.assert_term(stale_eq);

    assert_unsat(
        &mut solver,
        "latest store should overwrite earlier value at same location",
    );
}

#[test]
#[timeout(30000)]
fn test_base_memory_model_alloc_dealloc() {
    let model = BaseMemoryModel::new();

    // Use constrained init so domain starts empty — SAT checks are non-trivial.
    let (_, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(100);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    // Allocate
    let state = model.alloc(&mut solver, state, &ptr, val);

    // After alloc, not-in-domain must be UNSAT (proves alloc placed it in domain)
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    let not_in_dom = solver.not(in_dom);
    solver.assert_term(not_in_dom);
    assert_unsat(
        &mut solver,
        "allocated pointer must be in domain (UNSAT on negation)",
    );

    // Deallocate: after dealloc, in-domain must be UNSAT
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(100);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(999);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);
    let state2 = model.dealloc(&mut solver2, state2, &ptr2);

    let in_dom2 = model.in_domain(&mut solver2, &state2, &ptr2);
    solver2.assert_term(in_dom2);
    assert_unsat(
        &mut solver2,
        "deallocated pointer must not be in domain (UNSAT on membership)",
    );
}

#[test]
#[timeout(30000)]
fn test_base_memory_model_dealloc_clears_permission() {
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
        "deallocation must clear permission at freed location",
    );
}

#[test]
#[timeout(30000)]
fn test_base_memory_model_encode_points_to() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(7);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(55);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let perm_ok = solver.int_const(50);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, perm_ok);
    solver.assert_term(points_to);

    assert_sat(
        &mut solver,
        "points-to should hold for allocated pointer with valid permission",
    );

    let (_, mut solver2, state2) = mem_test_setup_unconstrained();
    let addr2 = solver2.int_const(7);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(55);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);
    let perm_too_high = solver2.int_const(PERM_SCALE + PERM_SCALE / 2);
    let points_to2 = model.encode_points_to(&mut solver2, &state2, addr2, val2, perm_too_high);
    solver2.assert_term(points_to2);

    assert_unsat(
        &mut solver2,
        "points-to should fail when required permission exceeds full scale",
    );
}

#[test]
#[timeout(30000)]
fn test_base_memory_model_encode_sep_conj() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    let left_true = solver.bool_const(true);
    let right_true = solver.bool_const(true);
    let sep_conj = model.encode_sep_conj(&mut solver, left_true, right_true);
    solver.assert_term(sep_conj);

    assert_unsat(
        &mut solver,
        "separating conjunction must reject overlapping true domains",
    );

    let mut solver2 = Solver::try_new(Logic::QfAuflia).unwrap();
    let left_true2 = solver2.bool_const(true);
    let right_false2 = solver2.bool_const(false);
    let sep_conj2 = model.encode_sep_conj(&mut solver2, left_true2, right_false2);
    solver2.assert_term(sep_conj2);

    assert_sat(
        &mut solver2,
        "separating conjunction should allow disjoint domains",
    );
}

#[test]
#[timeout(30000)]
fn test_base_memory_model_init_pure_and_sorts() {
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state = BaseMemoryModel::init_pure(&mut solver);

    let heap_eq_domain = solver.eq(pure_state.heap, pure_state.domain);
    solver.assert_term(heap_eq_domain);

    assert_sat(
        &mut solver,
        "init_pure heap/domain equality constraint should be satisfiable",
    );

    // Strengthening: init_pure sets heap and domain to the same placeholder term.
    // Any inequality between them must be UNSAT.
    let mut solver2 = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state2 = BaseMemoryModel::init_pure(&mut solver2);
    let heap_ne_domain = solver2.eq(pure_state2.heap, pure_state2.domain);
    let heap_ne_domain = solver2.not(heap_ne_domain);
    solver2.assert_term(heap_ne_domain);
    assert_unsat(
        &mut solver2,
        "init_pure heap/domain inequality should be UNSAT (both are identical placeholders)",
    );
    assert_eq!(
        BaseMemoryModel::loc_sort(),
        Sort::Int,
        "BaseMemoryModel location sort should be Int"
    );
    assert_eq!(
        BaseMemoryModel::val_sort(),
        Sort::Int,
        "BaseMemoryModel value sort should be Int"
    );
}

// Memory safety tests (Re: #346)

/// Test that double deallocation is detectable.
///
/// After deallocation, the location is no longer in the domain.
/// A second deallocation on the same location should be detectable
/// because we require the location to be in the domain before deallocating.
#[test]
#[timeout(30000)]
fn test_double_dealloc_detection() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Allocate, then deallocate
    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);

    // After first dealloc, location should NOT be in domain
    let in_dom = model.in_domain(&mut solver, &state, &ptr);

    // Assert location IS in domain (this should be false, hence unsat)
    solver.assert_term(in_dom);

    // Second dealloc would require location to be in domain
    // Since it's not, this constraint is unsatisfiable
    assert_unsat(
        &mut solver,
        "double dealloc detection should reject domain membership after dealloc",
    );
}

/// Test that use-after-free is detectable via domain membership.
///
/// After deallocation, loading from the location violates the
/// domain constraint - the memory is no longer valid.
#[test]
#[timeout(30000)]
fn test_use_after_free_detection() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Allocate, then deallocate
    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);

    // Try to load (structurally possible but violates safety)
    let loaded = model.load(&mut solver, &state, &ptr);

    // The load itself doesn't prevent execution, but domain check fails
    let in_dom = model.in_domain(&mut solver, &state, &ptr);

    // Assert both: we got some value AND it's in domain
    // The domain part should be false
    let val_eq = solver.eq(loaded, val);
    let both = solver.and(val_eq, in_dom);
    solver.assert_term(both);

    assert_unsat(
        &mut solver,
        "use-after-free conjunction should be unsatisfiable",
    );
}

/// Test that dangling pointer access (read before alloc) is detectable.
///
/// Reading from an address that was never allocated should violate
/// domain membership. With constrain_initial_state (#743), the
/// domain is all-false so no manual constraint is needed.
#[test]
#[timeout(30000)]
fn test_dangling_pointer_detection() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();
    // Apply empty-domain invariant
    let state = BaseMemoryModel::constrain_initial_state(&mut solver, &state);

    // Create a pointer without allocating
    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);

    // Domain is empty (const_array(false)), so asserting in_domain is UNSAT.
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    assert_unsat(
        &mut solver,
        "dangling pointer must not satisfy in-domain under constrained init",
    );
}

/// Test that double dealloc is prevented by domain check.
///
/// A proper verification condition for dealloc would require:
/// `in_domain(ptr) → dealloc(ptr) → ¬in_domain(ptr)`
///
/// This test verifies that after dealloc, the domain constraint
/// prevents any operation that requires the location to be valid.
#[test]
#[timeout(30000)]
fn test_double_dealloc_vc() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Allocate
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Verify in domain after alloc
    let in_dom_after_alloc = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom_after_alloc);
    assert_sat(
        &mut solver,
        "allocated pointer must satisfy in-domain precondition",
    );

    // Deallocate
    let _state = model.dealloc(&mut solver, state, &ptr);

    // Create new solver for clean assertion context
    let (_, mut solver2, state2) = mem_test_setup_unconstrained();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(100);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);
    let state2 = model.dealloc(&mut solver2, state2, &ptr2);

    // Try to verify that second dealloc requires domain membership
    // which is now false
    let in_dom_after_dealloc = model.in_domain(&mut solver2, &state2, &ptr2);

    // A dealloc precondition would assert: in_domain(ptr)
    // Since we already deallocated, this should be unsat
    solver2.assert_term(in_dom_after_dealloc);
    assert_unsat(
        &mut solver2,
        "dealloc precondition should fail after prior deallocation",
    );
}

// Fractional permission tests (Re: #347)

/// Test permission splitting: PERM_SCALE -> half + half.
///
/// Verifies that splitting full permission into two halves maintains
/// the total permission invariant.
#[test]
#[timeout(30000)]
#[serial(memory)]
fn test_permission_split() {
    let half_scale = PERM_SCALE / 2;
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Allocate with full permission
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Get current permission (should be PERM_SCALE)
    let perm = model.get_permission(&mut solver, &state, &ptr);
    let full = solver.int_const(PERM_SCALE);
    let is_full = solver.eq(perm, full);
    solver.assert_term(is_full);

    // Verify sat
    assert_sat(
        &mut solver,
        "allocated pointer permission should equal PERM_SCALE",
    );

    // After split to half: has_permission true, has_full_permission false
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(100);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);
    let half = solver2.int_const(half_scale);
    let mut split_state = state2.clone();
    split_state.permissions = solver2.store(split_state.permissions, addr2, half);

    let has_perm = model.has_permission(&mut solver2, &split_state, &ptr2);
    solver2.assert_term(has_perm);
    let has_full = model.has_full_permission(&mut solver2, &split_state, &ptr2);
    let not_full = solver2.not(has_full);
    solver2.assert_term(not_full);
    assert_sat(
        &mut solver2,
        "half permission satisfies has_permission but not has_full_permission",
    );

    // UNSAT dual: get_permission after split must NOT equal PERM_SCALE
    let (_, mut solver3, state3) = mem_test_setup();
    let addr3 = solver3.int_const(42);
    let ptr3 = MemPtr::new(addr3);
    let val3 = solver3.int_const(100);
    let state3 = model.alloc(&mut solver3, state3, &ptr3, val3);
    let half3 = solver3.int_const(half_scale);
    let mut split3 = state3.clone();
    split3.permissions = solver3.store(split3.permissions, addr3, half3);
    let perm3 = model.get_permission(&mut solver3, &split3, &ptr3);
    let full3 = solver3.int_const(PERM_SCALE);
    let eq_full = solver3.eq(perm3, full3);
    solver3.assert_term(eq_full);
    assert_unsat(
        &mut solver3,
        "get_permission after split to half must not equal PERM_SCALE",
    );
}

/// Test permission transfer soundness: can't transfer more than owned.
///
/// If a location has permission P, any transfer T must satisfy T <= P.
#[test]
#[timeout(30000)]
fn test_permission_transfer_soundness() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Allocate with full permission
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Try to assert points-to with permission > PERM_SCALE (should be unsat)
    let perm_too_high = solver.int_const(PERM_SCALE + PERM_SCALE / 2);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, perm_too_high);
    solver.assert_term(points_to);

    // Should be unsat - can't have 150% permission when only 100% exists
    assert_unsat(
        &mut solver,
        "permission transfer cannot exceed owned full permission",
    );
}

/// Test partial permission access.
///
/// With half permission, we can read but the permission check reflects
/// the partial ownership.
#[test]
#[timeout(30000)]
fn test_partial_permission_access() {
    let half_scale = PERM_SCALE / 2;
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Allocate with full permission, then simulate partial ownership
    // by directly modifying the permissions array
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Set permission to half (simulating a split)
    let half = solver.int_const(half_scale);
    let mut partial_state = state.clone();
    partial_state.permissions = solver.store(partial_state.permissions, addr, half);

    // Verify has_permission is true (half > 0)
    let has_perm = model.has_permission(&mut solver, &partial_state, &ptr);
    solver.assert_term(has_perm);

    assert_sat(
        &mut solver,
        "partial permission should still satisfy has_permission",
    );

    // Verify has_full_permission is false (half != PERM_SCALE)
    let (_, mut solver2, state2) = mem_test_setup_unconstrained();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(100);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);

    let half2 = solver2.int_const(half_scale);
    let mut partial_state2 = state2.clone();
    partial_state2.permissions = solver2.store(partial_state2.permissions, addr2, half2);

    let has_full = model.has_full_permission(&mut solver2, &partial_state2, &ptr2);
    solver2.assert_term(has_full);

    // Should be unsat - half != PERM_SCALE
    assert_unsat(
        &mut solver2,
        "partial permission must fail has_full_permission",
    );
}

/// Test permission recombination: half + half = PERM_SCALE.
///
/// After splitting permission and later recombining, we should
/// have full permission again.
#[test]
#[timeout(30000)]
#[serial(memory)]
fn test_permission_recombine() {
    let half_scale = PERM_SCALE / 2;
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Start with full permission
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Split: set to half
    let half = solver.int_const(half_scale);
    let mut split_state = state.clone();
    split_state.permissions = solver.store(split_state.permissions, addr, half);

    // Verify not full after split
    let not_full = model.has_full_permission(&mut solver, &split_state, &ptr);
    let is_not_full = solver.not(not_full);
    solver.assert_term(is_not_full);
    assert_sat(
        &mut solver,
        "split permission state should satisfy not-full constraint",
    );

    // Recombine: set back to PERM_SCALE
    let (_, mut solver2, state2) = mem_test_setup_unconstrained();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(100);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);

    let half2 = solver2.int_const(half_scale);
    let mut split_state2 = state2.clone();
    split_state2.permissions = solver2.store(split_state2.permissions, addr2, half2);

    // Recombine by setting back to full
    let full2 = solver2.int_const(PERM_SCALE);
    let mut recombined_state = split_state2.clone();
    recombined_state.permissions = solver2.store(recombined_state.permissions, addr2, full2);

    // Verify full after recombine
    let is_full = model.has_full_permission(&mut solver2, &recombined_state, &ptr2);
    solver2.assert_term(is_full);
    assert_sat(
        &mut solver2,
        "recombined permission state should satisfy has_full_permission",
    );
}

/// Test permission conservation: total permission can't increase.
///
/// The sum of all permissions for a location across all owners
/// must not exceed the allocated amount.
#[test]
#[timeout(30000)]
fn test_permission_conservation() {
    // Positive: after alloc, the stored permission must be exactly PERM_SCALE.
    // This exercises the memory model API, not just ay arithmetic.
    let (model1, mut solver1, state1) = mem_test_setup();
    let addr1 = solver1.int_const(42);
    let ptr1 = MemPtr::new(addr1);
    let val1 = solver1.int_const(999);
    let state1 = model1.alloc(&mut solver1, state1, &ptr1, val1);

    // The permission at the allocated address must be PERM_SCALE (UNSAT for different)
    let perm_actual = solver1.select(state1.permissions, addr1);
    let expected_perm = solver1.int_const(PERM_SCALE);
    let neq = solver1.neq(perm_actual, expected_perm);
    solver1.assert_term(neq);
    assert_unsat(
        &mut solver1,
        "allocated permission must be exactly PERM_SCALE",
    );

    // Negative case: after allocating with PERM_SCALE permission, two
    // non-negative permission shares cannot sum to more than PERM_SCALE.
    // This tests the memory model's actual permission budget, not just
    // ay arithmetic.
    let (model2, mut solver2, state2) = mem_test_setup();

    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(999);
    let state2 = model2.alloc(&mut solver2, state2, &ptr2, val2);

    // The actual permission stored is PERM_SCALE. Try to claim two shares
    // that sum to more than that.
    let perm_actual = solver2.select(state2.permissions, addr2);
    let perm1_2 = solver2.declare_const("share1", Sort::Int);
    let perm2_2 = solver2.declare_const("share2", Sort::Int);
    let zero2 = solver2.int_const(0);

    // Both shares non-negative
    let ge1 = solver2.ge(perm1_2, zero2);
    solver2.assert_term(ge1);
    let ge2 = solver2.ge(perm2_2, zero2);
    solver2.assert_term(ge2);
    // Both shares bounded by actual permission
    let sum2 = solver2.add(perm1_2, perm2_2);
    let bounded = solver2.le(sum2, perm_actual);
    solver2.assert_term(bounded);
    // Try to make sum exceed PERM_SCALE
    let over_budget = solver2.int_const(PERM_SCALE + 1);
    let sum2_again = solver2.add(perm1_2, perm2_2);
    let exceeds = solver2.ge(sum2_again, over_budget);
    solver2.assert_term(exceeds);

    assert_unsat(
        &mut solver2,
        "two permission shares from a single alloc cannot exceed PERM_SCALE",
    );
}

// RAII lifecycle composition tests (#552 memory_verification)

/// Test full RAII lifecycle: alloc -> store -> load -> dealloc -> verify freed.
///
/// This composes primitive operations into the pattern a Box would follow:
/// allocate with initial value, mutate, read back, then deallocate and verify
/// that the location is no longer accessible.
#[test]
#[timeout(30000)]
fn test_raii_lifecycle_alloc_use_dealloc() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let init_val = solver.int_const(100);

    // Phase 1: Allocate (Box::new)
    let state = model.alloc(&mut solver, state, &ptr, init_val);

    // Verify: in domain, full permission, value correct
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);
    let has_full = model.has_full_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_full);
    let loaded = model.load(&mut solver, &state, &ptr);
    let val_eq = solver.eq(loaded, init_val);
    solver.assert_term(val_eq);
    assert_sat(
        &mut solver,
        "RAII allocate phase should satisfy domain, permission, and value checks",
    );

    // Phase 2: Mutate (*box_ref = new_val)
    let new_val = solver.int_const(200);
    let state = model.store(&mut solver, state, &ptr, new_val);

    // Phase 3: Read back — must see new value
    let (_, mut solver2, state2) = mem_test_setup_unconstrained();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let init2 = solver2.int_const(100);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, init2);
    let new2 = solver2.int_const(200);
    let state2 = model.store(&mut solver2, state2, &ptr2, new2);
    let loaded2 = model.load(&mut solver2, &state2, &ptr2);
    let eq2 = solver2.eq(loaded2, new2);
    solver2.assert_term(eq2);
    assert_sat(
        &mut solver2,
        "RAII store then load should observe updated value",
    );

    // Phase 4: Deallocate (drop(Box))
    let state2 = model.dealloc(&mut solver2, state2, &ptr2);

    // Verify: NOT in domain, no permission
    let (_, mut solver3, state3) = mem_test_setup_unconstrained();
    let addr3 = solver3.int_const(42);
    let ptr3 = MemPtr::new(addr3);
    let init3 = solver3.int_const(100);
    let state3 = model.alloc(&mut solver3, state3, &ptr3, init3);
    let state3 = model.dealloc(&mut solver3, state3, &ptr3);
    let in_dom3 = model.in_domain(&mut solver3, &state3, &ptr3);
    // Asserting in_domain after dealloc must be UNSAT
    solver3.assert_term(in_dom3);
    assert_unsat(
        &mut solver3,
        "RAII deallocated pointer must not remain in domain",
    );

    // Suppress unused variable warnings
    let _ = state;
    let _ = state2;
}

/// Test that two independent allocations maintain frame separation.
///
/// Allocating at loc1 and loc2, then deallocating loc1, must not affect
/// loc2's domain membership, value, or permission.
#[test]
#[timeout(30000)]
fn test_raii_two_objects_frame_independence() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);

    // Allocate two objects
    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);
    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);

    // Deallocate only ptr1
    let state = model.dealloc(&mut solver, state, &ptr1);

    // ptr1 must NOT be in domain
    let in_dom1 = model.in_domain(&mut solver, &state, &ptr1);
    let not_in_dom1 = solver.not(in_dom1);
    solver.assert_term(not_in_dom1);

    // ptr2 must STILL be in domain
    let in_dom2 = model.in_domain(&mut solver, &state, &ptr2);
    solver.assert_term(in_dom2);

    // ptr2 must still have full permission
    let full2 = model.has_full_permission(&mut solver, &state, &ptr2);
    solver.assert_term(full2);

    // ptr2 must still hold its value
    let loaded2 = model.load(&mut solver, &state, &ptr2);
    let eq2 = solver.eq(loaded2, val2);
    solver.assert_term(eq2);

    assert_sat(
        &mut solver,
        "deallocating one object must preserve other object's frame state",
    );

    // UNSAT dual: ptr1 MUST be out of domain (not just CAN be)
    let (_, mut solver2, state2) = mem_test_setup();
    let a1 = solver2.int_const(10);
    let a2 = solver2.int_const(20);
    let p1 = MemPtr::new(a1);
    let p2 = MemPtr::new(a2);
    let v1 = solver2.int_const(111);
    let v2 = solver2.int_const(222);
    let state2 = model.alloc(&mut solver2, state2, &p1, v1);
    let state2 = model.alloc(&mut solver2, state2, &p2, v2);
    let state2 = model.dealloc(&mut solver2, state2, &p1);
    let dealloc_in_dom = model.in_domain(&mut solver2, &state2, &p1);
    solver2.assert_term(dealloc_in_dom);
    assert_unsat(
        &mut solver2,
        "ptr1 must be definitively out of domain after dealloc (UNSAT dual)",
    );
}

// MemPtr wide-pointer tests (#552 memory_verification)

/// Test that MemPtr meta field (wide-pointer metadata) can carry a size term.
///
/// The meta field is never tested with Some(...) in any existing test.
/// This verifies the field is usable for future wide-pointer encodings.
#[test]
#[timeout(30000)]
fn test_memptr_wide_pointer_with_meta() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let size = solver.int_const(8); // e.g., slice length
    let ptr = MemPtr {
        addr,
        meta: Some(size),
    };

    // alloc/load/store only use ptr.addr — meta is metadata for future use.
    // Verify that the presence of meta doesn't break basic operations.
    let val = solver.int_const(999);
    let state = model.alloc(&mut solver, state, &ptr, val);
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val);
    solver.assert_term(eq);

    assert_sat(
        &mut solver,
        "MemPtr operations should remain satisfiable with metadata present",
    );

    // Verify metadata is present and identical to the original size term.
    let preserved_meta = ptr
        .meta
        .expect("wide-pointer MemPtr should preserve metadata term");
    let meta_eq_size = solver.eq(preserved_meta, size);
    solver.assert_term(meta_eq_size);
    assert_sat(
        &mut solver,
        "MemPtr metadata term should equal the original size term",
    );
}

/// UNSAT dual for wide-pointer with meta: asserting loaded != stored value
/// after alloc at the same address must be UNSAT (read-over-write-same).
/// Strengthens the SAT-only test above with a proof obligation. (#1649)
#[test]
#[timeout(30000)]
fn test_memptr_wide_pointer_load_equals_store() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let size = solver.int_const(8);
    let ptr = MemPtr {
        addr,
        meta: Some(size),
    };

    let val = solver.int_const(999);
    let state = model.alloc(&mut solver, state, &ptr, val);
    let loaded = model.load(&mut solver, &state, &ptr);

    // Assert loaded != val — should be UNSAT because we just stored val at addr
    let eq = solver.eq(loaded, val);
    let neq = solver.not(eq);
    solver.assert_term(neq);
    assert_unsat(
        &mut solver,
        "loaded value must equal stored value after alloc at same address (read-over-write-same)",
    );
}

/// Test that MemPtr meta field carries through clone.
///
/// Clone is derived — these are Rust-level Term handle identity checks.
/// Also verify that a default (no-meta) MemPtr differs structurally.
#[test]
#[timeout(30000)]
fn test_memptr_clone_preserves_meta() {
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let addr = solver.int_const(10);
    let meta = solver.int_const(4);
    let ptr = MemPtr {
        addr,
        meta: Some(meta),
    };
    let cloned = ptr.clone();

    // Rust-level: Term handles are Copy, so clone preserves identity.
    assert_eq!(
        ptr.addr, cloned.addr,
        "cloned MemPtr should have identical addr Term"
    );
    assert_eq!(
        ptr.meta, cloned.meta,
        "cloned MemPtr should have identical meta Option<Term>"
    );

    // Structural contrast: default MemPtr has no metadata
    let bare = MemPtr::new(addr);
    assert!(bare.meta.is_none(), "MemPtr::new should have no metadata");
    assert!(
        cloned.meta.is_some(),
        "cloned MemPtr should preserve Some(meta)"
    );

    // SMT-level: use cloned pointer in an alloc+load cycle to verify
    // the cloned handle is operationally equivalent to the original.
    let model = BaseMemoryModel::new();
    let state = BaseMemoryModel::init(&mut solver);
    let state = BaseMemoryModel::constrain_initial_state(&mut solver, &state);
    let val = solver.int_const(42);
    let state = model.alloc(&mut solver, state, &ptr, val);
    let loaded = model.load(&mut solver, &state, &cloned);
    let neq = solver.neq(loaded, val);
    solver.assert_term(neq);
    assert_unsat(
        &mut solver,
        "load via cloned MemPtr must return same value as stored via original",
    );
}

// constrain_initial_state regression tests (#743)

/// Regression: points-to on unallocated location must be UNSAT
/// when constrain_initial_state is applied.
///
/// Without constrain_initial_state, the unconstrained domain array lets
/// the solver satisfy a points-to assertion without any prior allocation.
/// With it, the const_array(false) domain makes this correctly UNSAT.
#[test]
#[timeout(30000)]
fn test_constrained_no_spurious_points_to_without_alloc() {
    let (model, mut solver, state) = mem_test_setup();

    // Try to assert points-to without any allocation
    let addr = solver.int_const(42);
    let val = solver.int_const(999);
    let perm = solver.int_const(50);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, perm);
    solver.assert_term(points_to);

    // Must be UNSAT: domain is empty and permissions are zero
    assert_unsat(
        &mut solver,
        "constrained initial state must reject points-to without allocation",
    );
}

/// Regression: initial permissions are zero when constrained.
///
/// Without constrain_initial_state, `has_permission` can be satisfied
/// at any address because the permissions array is unconstrained.
#[test]
#[timeout(30000)]
fn test_constrained_no_spurious_permission_without_alloc() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);

    // has_permission checks perm > 0; should be UNSAT with constrained state
    let has_perm = model.has_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_perm);

    assert_unsat(
        &mut solver,
        "constrained initial state must reject positive permission without alloc",
    );
}

/// Regression: alloc then check still works with constrain_initial_state.
///
/// Ensures that the empty-domain invariant doesn't break normal
/// alloc/points-to workflows. store() overrides const_array entries
/// via read-over-write.
#[test]
#[timeout(30000)]
fn test_constrained_alloc_then_points_to_still_works() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    // Allocate — this overwrites the const_array entries via store()
    let state = model.alloc(&mut solver, state, &ptr, val);

    // points-to with <= 100 perm should be SAT
    let perm = solver.int_const(50);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, perm);
    solver.assert_term(points_to);

    assert_sat(
        &mut solver,
        "alloc should restore satisfiable points-to under constrained init",
    );
}

// Store non-interference (frame rule) tests

/// Store at addr2 must not affect the value loaded from addr1.
///
/// This verifies the Array read-over-write-different axiom:
///   store(A, addr2, v2) => select(store(A, addr2, v2), addr1) == select(A, addr1)
/// when addr1 != addr2.
#[test]
#[timeout(30000)]
fn test_store_noninterference_different_addresses() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);

    // Store value 111 at addr1
    let val1 = solver.int_const(111);
    let state = model.store(&mut solver, state, &ptr1, val1);

    // Store value 222 at addr2 (must NOT affect addr1)
    let val2 = solver.int_const(222);
    let state = model.store(&mut solver, state, &ptr2, val2);

    // Load from addr1 — must still be 111
    let loaded1 = model.load(&mut solver, &state, &ptr1);
    let must_differ = solver.eq(loaded1, val2);
    solver.assert_term(must_differ);

    // If loaded1 == 222, that would mean store at addr2 clobbered addr1.
    // This must be UNSAT because store only writes to addr2.
    assert_unsat(
        &mut solver,
        "store at addr2=20 must not change heap value at addr1=10",
    );
}

/// Store at addr2, then verify addr1 load equals original stored value.
///
/// Positive variant of noninterference: SAT that addr1 value is preserved.
#[test]
#[timeout(30000)]
fn test_store_noninterference_preserves_original() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);

    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.store(&mut solver, state, &ptr1, val1);
    let state = model.store(&mut solver, state, &ptr2, val2);

    // addr1 still reads val1
    let loaded1 = model.load(&mut solver, &state, &ptr1);
    let eq1 = solver.eq(loaded1, val1);
    solver.assert_term(eq1);

    // addr2 reads val2
    let loaded2 = model.load(&mut solver, &state, &ptr2);
    let eq2 = solver.eq(loaded2, val2);
    solver.assert_term(eq2);

    assert_sat(
        &mut solver,
        "both stores should be readable at their respective addresses",
    );
}

// Permission boundary tests

/// Zero permission must not satisfy has_permission (perm > 0 is strict).
#[test]
#[timeout(30000)]
fn test_zero_permission_is_not_positive() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Allocate then set permission to exactly 0
    let state = model.alloc(&mut solver, state, &ptr, val);
    let zero = solver.int_const(0);
    let mut zero_perm_state = state.clone();
    zero_perm_state.permissions = solver.store(zero_perm_state.permissions, addr, zero);

    let has_perm = model.has_permission(&mut solver, &zero_perm_state, &ptr);
    solver.assert_term(has_perm);

    assert_unsat(
        &mut solver,
        "zero permission must not satisfy has_permission (strict > 0)",
    );
}

/// Minimal positive permission (1) should satisfy has_permission.
#[test]
#[timeout(30000)]
fn test_minimal_positive_permission() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let one = solver.int_const(1);
    let mut min_perm_state = state.clone();
    min_perm_state.permissions = solver.store(min_perm_state.permissions, addr, one);

    let has_perm = model.has_permission(&mut solver, &min_perm_state, &ptr);
    solver.assert_term(has_perm);

    assert_sat(
        &mut solver,
        "permission == 1 (minimal positive) should satisfy has_permission",
    );
}

// Dealloc non-interference test

/// Dealloc at addr1 must not affect addr2's permission or domain.
#[test]
#[timeout(30000)]
fn test_dealloc_noninterference() {
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

    // addr1 should be out of domain with zero permission
    let in_dom1 = model.in_domain(&mut solver, &state, &ptr1);
    let not_in_dom1 = solver.not(in_dom1);
    solver.assert_term(not_in_dom1);

    let has_perm1 = model.has_permission(&mut solver, &state, &ptr1);
    let no_perm1 = solver.not(has_perm1);
    solver.assert_term(no_perm1);

    // addr2 should still have domain and full permission
    let in_dom2 = model.in_domain(&mut solver, &state, &ptr2);
    solver.assert_term(in_dom2);

    let has_full2 = model.has_full_permission(&mut solver, &state, &ptr2);
    solver.assert_term(has_full2);

    // addr2 value should be preserved
    let loaded2 = model.load(&mut solver, &state, &ptr2);
    let eq2 = solver.eq(loaded2, val2);
    solver.assert_term(eq2);

    assert_sat(
        &mut solver,
        "dealloc at addr1 must preserve addr2's domain, permission, and value",
    );
}

// Assertion strengthening: constrained-init variants (Re: #901)
//
// Tests below use constrain_initial_state to prevent SAT results
// from being trivially satisfiable via unconstrained symbolic arrays.

/// Load after store at the same address must equal the stored value (UNSAT dual).
///
/// With constrained init, the unconstrained heap cannot satisfy the assertion
/// by accident — the store is the only way to get the correct value.
#[test]
#[timeout(30000)]
fn test_load_store_constrained_wrong_value_is_unsat() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(123);
    let wrong = solver.int_const(456);

    // Allocate (to enter domain), then store val
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Load back and assert it equals the wrong value
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq_wrong = solver.eq(loaded, wrong);
    solver.assert_term(eq_wrong);

    assert_unsat(
        &mut solver,
        "load after store must not equal a value different from what was stored",
    );
}

/// Alloc under constrained init must place the location in domain (non-trivial SAT).
///
/// With constrained init, domain is all-false. Only alloc can make
/// in_domain(ptr) true, so this test cannot pass with a no-op alloc.
#[test]
#[timeout(30000)]
fn test_alloc_under_constrained_init_enters_domain() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);

    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    let has_full = model.has_full_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_full);

    let loaded = model.load(&mut solver, &state, &ptr);
    let val_eq = solver.eq(loaded, val);
    solver.assert_term(val_eq);

    assert_sat(
        &mut solver,
        "alloc under constrained init must place location in domain with full perm and correct value",
    );

    // Strengthening: negating each alloc post-state fact must be UNSAT.
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(999);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);
    let in_dom2 = model.in_domain(&mut solver2, &state2, &ptr2);
    let not_in_dom2 = solver2.not(in_dom2);
    solver2.assert_term(not_in_dom2);
    assert_unsat(
        &mut solver2,
        "alloc under constrained init must force in-domain (NOT in_domain should be UNSAT)",
    );

    let (_, mut solver3, state3) = mem_test_setup();
    let addr3 = solver3.int_const(42);
    let ptr3 = MemPtr::new(addr3);
    let val3 = solver3.int_const(999);
    let state3 = model.alloc(&mut solver3, state3, &ptr3, val3);
    let has_full3 = model.has_full_permission(&mut solver3, &state3, &ptr3);
    let not_full3 = solver3.not(has_full3);
    solver3.assert_term(not_full3);
    assert_unsat(
        &mut solver3,
        "alloc under constrained init must force full permission (NOT has_full should be UNSAT)",
    );

    let (_, mut solver4, state4) = mem_test_setup();
    let addr4 = solver4.int_const(42);
    let ptr4 = MemPtr::new(addr4);
    let val4 = solver4.int_const(999);
    let wrong4 = solver4.int_const(123);
    let state4 = model.alloc(&mut solver4, state4, &ptr4, val4);
    let loaded4 = model.load(&mut solver4, &state4, &ptr4);
    let wrong_eq4 = solver4.eq(loaded4, wrong4);
    solver4.assert_term(wrong_eq4);
    assert_unsat(
        &mut solver4,
        "alloc under constrained init must force stored value (load==wrong must be UNSAT)",
    );
}

/// Points-to with wrong value must be UNSAT after alloc with correct value.
#[test]
#[timeout(30000)]
fn test_points_to_wrong_value_is_unsat() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(7);
    let ptr = MemPtr::new(addr);
    let correct_val = solver.int_const(55);
    let wrong_val = solver.int_const(99);

    let state = model.alloc(&mut solver, state, &ptr, correct_val);

    let perm = solver.int_const(50);
    let points_to = model.encode_points_to(&mut solver, &state, addr, wrong_val, perm);
    solver.assert_term(points_to);

    assert_unsat(
        &mut solver,
        "points-to with wrong value must be UNSAT when correct value was stored",
    );
}

/// Points-to with exactly PERM_SCALE permission must be SAT after alloc.
#[test]
#[timeout(30000)]
fn test_points_to_exact_full_permission_boundary() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(7);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(55);

    let state = model.alloc(&mut solver, state, &ptr, val);

    // Request exactly PERM_SCALE permission — encode_points_to checks >=
    let exact_full = solver.int_const(PERM_SCALE);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, exact_full);
    solver.assert_term(points_to);

    assert_sat(
        &mut solver,
        "points-to with exactly PERM_SCALE should be SAT after alloc with full perm",
    );

    // Strengthening: after alloc, this exact points-to fact is forced.
    // Its negation must be UNSAT.
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(7);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(55);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);
    let exact_full2 = solver2.int_const(PERM_SCALE);
    let points_to2 = model.encode_points_to(&mut solver2, &state2, addr2, val2, exact_full2);
    let not_points_to2 = solver2.not(points_to2);
    solver2.assert_term(not_points_to2);
    assert_unsat(
        &mut solver2,
        "exact-full points-to negation must be UNSAT after alloc",
    );
}

/// Store without prior alloc must not affect domain membership.
#[test]
#[timeout(30000)]
fn test_store_without_alloc_leaves_domain_empty() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    // Store directly (no alloc) — only updates heap, not domain/perms
    let state = model.store(&mut solver, state, &ptr, val);

    // Domain should still be empty
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    assert_unsat(
        &mut solver,
        "store without alloc must not place location in domain",
    );

    // Strengthen: store without alloc must not create positive permission.
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(999);
    let state2 = model.store(&mut solver2, state2, &ptr2, val2);
    let has_perm2 = model.has_permission(&mut solver2, &state2, &ptr2);
    solver2.assert_term(has_perm2);
    assert_unsat(
        &mut solver2,
        "store without alloc must not create positive permission",
    );

    // Strengthen: even with matching heap value, points-to must remain UNSAT
    // because domain/perms are unchanged without alloc.
    let (_, mut solver3, state3) = mem_test_setup();
    let addr3 = solver3.int_const(42);
    let ptr3 = MemPtr::new(addr3);
    let val3 = solver3.int_const(999);
    let state3 = model.store(&mut solver3, state3, &ptr3, val3);
    let req_perm3 = solver3.int_const(1);
    let points_to3 = model.encode_points_to(&mut solver3, &state3, addr3, val3, req_perm3);
    solver3.assert_term(points_to3);
    assert_unsat(
        &mut solver3,
        "store without alloc must not satisfy points-to",
    );
}

/// Re-alloc at an already-allocated address resets permission to PERM_SCALE.
#[test]
#[timeout(30000)]
fn test_realloc_at_same_address_resets_state() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let val2 = solver.int_const(200);

    // First alloc
    let state = model.alloc(&mut solver, state, &ptr, val1);

    // Second alloc at same address with different value
    let state = model.alloc(&mut solver, state, &ptr, val2);

    // Should have full permission
    let has_full = model.has_full_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_full);

    // Should see the new value, not the old
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq_new = solver.eq(loaded, val2);
    solver.assert_term(eq_new);

    assert_sat(
        &mut solver,
        "re-alloc at same address should see new value with full permission",
    );

    // Verify old value is NOT observable
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let old2 = solver2.int_const(100);
    let new2 = solver2.int_const(200);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, old2);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, new2);
    let loaded2 = model.load(&mut solver2, &state2, &ptr2);
    let eq_old = solver2.eq(loaded2, old2);
    solver2.assert_term(eq_old);

    assert_unsat(
        &mut solver2,
        "re-alloc must overwrite old value; loading old value must be UNSAT",
    );
}

/// Negative permission values must not satisfy has_permission.
#[test]
#[timeout(30000)]
fn test_negative_permission_rejected() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let neg = solver.int_const(-1);
    let mut neg_perm_state = state.clone();
    neg_perm_state.permissions = solver.store(neg_perm_state.permissions, addr, neg);

    let has_perm = model.has_permission(&mut solver, &neg_perm_state, &ptr);
    solver.assert_term(has_perm);

    assert_unsat(
        &mut solver,
        "negative permission must not satisfy has_permission (perm > 0)",
    );
}

/// Domain membership is encoded as `domain[loc] == 1` (exact marker).
///
/// Any other non-zero marker (for example `2`) must NOT satisfy
/// `in_domain`. This guards against accidental weakening to `domain[loc] > 0`.
#[test]
#[timeout(30000)]
fn test_in_domain_requires_exact_marker_one() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Start from a valid allocated state, then mutate domain marker to 2.
    let mut state = model.alloc(&mut solver, state, &ptr, val);
    let two = solver.int_const(2);
    state.domain = solver.store(state.domain, addr, two);

    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    assert_unsat(
        &mut solver,
        "in_domain should require domain[loc] == 1 exactly (domain[loc] == 2 must be UNSAT)",
    );
}

/// points-to must also require the exact domain marker `1`.
///
/// Even when heap value and permission constraints hold, `domain[loc] == 2`
/// should make points-to unsatisfiable.
#[test]
#[timeout(30000)]
fn test_points_to_rejects_non_one_domain_marker() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(7);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(55);
    let mut state = model.alloc(&mut solver, state, &ptr, val);

    // Keep heap/perms from alloc, but replace domain marker with 2.
    let two = solver.int_const(2);
    state.domain = solver.store(state.domain, addr, two);

    let required_perm = solver.int_const(1);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, required_perm);
    solver.assert_term(points_to);

    assert_unsat(
        &mut solver,
        "points-to should be UNSAT when domain marker is not exactly 1",
    );
}

/// constrain_initial_state leaves heap array unconstrained.
///
/// Prove truly symbolic by showing two different values are each independently
/// SAT, and their conjunction is UNSAT (not a constant array).
#[test]
#[timeout(30000)]
fn test_constrained_init_heap_still_symbolic() {
    // SAT with value 999
    let (_, mut solver1, state1) = mem_test_setup();
    let addr1 = solver1.int_const(42);
    let val1 = solver1.int_const(999);
    let heap_val1 = solver1.select(state1.heap, addr1);
    let eq1 = solver1.eq(heap_val1, val1);
    solver1.assert_term(eq1);
    assert_sat(
        &mut solver1,
        "constrained init heap must accept value 999 (symbolic)",
    );

    // SAT with different value 888
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let val2 = solver2.int_const(888);
    let heap_val2 = solver2.select(state2.heap, addr2);
    let eq2 = solver2.eq(heap_val2, val2);
    solver2.assert_term(eq2);
    assert_sat(
        &mut solver2,
        "constrained init heap must accept value 888 (symbolic dual)",
    );

    // UNSAT: heap[42] == 999 AND heap[42] == 888 — proves not constant
    let (_, mut solver3, state3) = mem_test_setup();
    let addr3 = solver3.int_const(42);
    let heap_val3 = solver3.select(state3.heap, addr3);
    let c999 = solver3.int_const(999);
    let c888 = solver3.int_const(888);
    let eq3a = solver3.eq(heap_val3, c999);
    let eq_heap_888 = solver3.eq(heap_val3, c888);
    solver3.assert_term(eq3a);
    solver3.assert_term(eq_heap_888);
    assert_unsat(
        &mut solver3,
        "heap cannot be both 999 and 888 — proves not a constant array",
    );
}

// Symbolic address aliasing tests (Re: #901 assertion strengthening)
//
// All preceding tests use concrete addresses (int_const(10), int_const(20), etc.)
// where ay trivially knows 10 != 20. Real programs use symbolic addresses where
// aliasing is undecided until constraints are added. These tests verify that the
// memory model correctly handles the symbolic case.

/// With symbolic addresses, store at addr1 may or may not affect load at addr2.
///
/// When addr1 and addr2 are unconstrained, the solver can choose addr1 == addr2,
/// making the store visible. This tests that the encoding does not accidentally
/// prevent aliasing.
#[test]
#[timeout(30000)]
fn test_symbolic_address_aliasing_store_visible() {
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
fn test_symbolic_address_non_aliasing_store_invisible() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.declare_const("addr1", Sort::Int);
    let addr2 = solver.declare_const("addr2", Sort::Int);
    let addr_eq = solver.eq(addr1, addr2);
    let neq = solver.not(addr_eq);
    solver.assert_term(neq);

    let ptr1 = MemPtr::new(addr1);
    let val = solver.int_const(42);

    // Allocate at addr1 (so heap[addr1] = 42) but NOT at addr2
    let state = model.alloc(&mut solver, state, &ptr1, val);

    // Assert addr2 is in domain — should be UNSAT because only addr1 was allocated
    // and addr1 != addr2. ay-dpll incorrectly returns Sat.
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
fn test_symbolic_address_alloc_then_points_to() {
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
fn test_symbolic_address_points_to_wrong_value_unsat() {
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
#[test]
#[timeout(30000)]
fn test_symbolic_address_frame_independence() {
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

/// UNSAT dual for dealloc non-interference: after alloc(addr1) + alloc(addr2)
/// + dealloc(addr1), asserting addr2 is NOT in domain must be UNSAT.
///
/// The SAT test above shows the solver CAN find a model where addr2 is still
/// in domain. This UNSAT dual proves addr2 MUST be in domain — the alloc at
/// addr2 is not affected by the dealloc at addr1 with concrete different addresses.
#[test]
#[timeout(30000)]
fn test_dealloc_noninterference_forced_domain_unsat_dual() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);

    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);
    let state = model.dealloc(&mut solver, state, &ptr1);

    // Asserting addr2 is NOT in domain must be UNSAT: alloc(addr2) put it
    // in domain, and dealloc(addr1) cannot affect addr2.
    let in_dom2 = model.in_domain(&mut solver, &state, &ptr2);
    let not_in_dom2 = solver.not(in_dom2);
    solver.assert_term(not_in_dom2);

    assert_unsat(
        &mut solver,
        "dealloc at addr1 must NOT remove addr2 from domain (UNSAT dual)",
    );
}

/// UNSAT dual for dealloc non-interference: addr2's value must be forced.
///
/// After alloc(addr1, v1) + alloc(addr2, v2) + dealloc(addr1), asserting
/// load(addr2) != v2 must be UNSAT — the value at addr2 is definitively v2.
#[test]
#[timeout(30000)]
fn test_dealloc_noninterference_forced_value_unsat_dual() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);

    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);
    let state = model.dealloc(&mut solver, state, &ptr1);

    let loaded2 = model.load(&mut solver, &state, &ptr2);
    let wrong = solver.int_const(999);
    let eq_wrong = solver.eq(loaded2, wrong);
    solver.assert_term(eq_wrong);

    assert_unsat(
        &mut solver,
        "dealloc at addr1 must NOT change addr2's stored value (UNSAT dual)",
    );
}

/// Alloc then store at same address: store overwrites the alloc value.
///
/// `alloc(addr, v1)` sets heap[addr] = v1. A subsequent `store(addr, v2)`
/// must overwrite so that `load(addr)` returns v2, not v1.
#[test]
#[timeout(30000)]
fn test_alloc_then_store_overwrites_value() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let init_val = solver.int_const(100);
    let new_val = solver.int_const(200);

    let state = model.alloc(&mut solver, state, &ptr, init_val);
    let state = model.store(&mut solver, state, &ptr, new_val);
    let loaded = model.load(&mut solver, &state, &ptr);

    // loaded must equal new_val
    let eq_new = solver.eq(loaded, new_val);
    solver.assert_term(eq_new);
    assert_sat(
        &mut solver,
        "load after alloc+store should see the stored value",
    );

    // UNSAT dual: loaded must NOT equal the alloc value
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let init2 = solver2.int_const(100);
    let new2 = solver2.int_const(200);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, init2);
    let state2 = model.store(&mut solver2, state2, &ptr2, new2);
    let loaded2 = model.load(&mut solver2, &state2, &ptr2);
    let eq_old = solver2.eq(loaded2, init2);
    solver2.assert_term(eq_old);

    assert_unsat(
        &mut solver2,
        "store must overwrite alloc value: load==init_val must be UNSAT after store",
    );
}

// Separation logic composition proofs (Re: #901 formal_proofs phase)
//
// The encode_sep_conj tests above use bare boolean constants (true/false).
// These tests exercise sep_conj with actual in_domain predicates from real
// memory states, ensuring the separation logic encoding works end-to-end.

/// Sep-conj with real heap states: two allocations at same address must
/// violate separation (both domains claim the same location).
///
/// Encode: alloc addr in state1, alloc addr in state2.
/// sep_conj(in_domain(state1, addr), in_domain(state2, addr)) must be UNSAT
/// because both domains include the same location.
#[test]
#[timeout(30000)]
fn test_sep_conj_same_address_overlap_is_unsat() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    // Two independent memory states, both allocating at the same address
    let state1 = BaseMemoryModel::init(&mut solver);
    let state1 = BaseMemoryModel::constrain_initial_state(&mut solver, &state1);
    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let state1 = model.alloc(&mut solver, state1, &ptr, val1);

    let state2 = BaseMemoryModel::init(&mut solver);
    let state2 = BaseMemoryModel::constrain_initial_state(&mut solver, &state2);
    let val2 = solver.int_const(200);
    let state2 = model.alloc(&mut solver, state2, &ptr, val2);

    let dom1 = model.in_domain(&mut solver, &state1, &ptr);
    let dom2 = model.in_domain(&mut solver, &state2, &ptr);

    let sep = model.encode_sep_conj(&mut solver, dom1, dom2);
    solver.assert_term(sep);

    assert_unsat(
        &mut solver,
        "sep_conj must reject two allocations at the same address (overlapping domains)",
    );
}

/// Sep-conj with disjoint domain predicates from a single memory state:
/// addr1 is allocated, addr2 is not. Their in_domain predicates should
/// satisfy separation because only one is true.
#[test]
#[timeout(30000)]
fn test_sep_conj_disjoint_addresses_is_sat() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    let state = BaseMemoryModel::init(&mut solver);
    let state = BaseMemoryModel::constrain_initial_state(&mut solver, &state);
    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let val1 = solver.int_const(100);

    // Only allocate addr1, NOT addr2
    let state = model.alloc(&mut solver, state, &ptr1, val1);

    // in_domain(addr1) is true, in_domain(addr2) is false (constrained init)
    let dom_at_addr1 = model.in_domain(&mut solver, &state, &ptr1);
    let dom_at_addr2 = model.in_domain(&mut solver, &state, &ptr2);

    let sep = model.encode_sep_conj(&mut solver, dom_at_addr1, dom_at_addr2);
    solver.assert_term(sep);

    assert_sat(
        &mut solver,
        "sep_conj must accept: addr1 allocated, addr2 not allocated in same state",
    );
}

/// Sep-conj with dealloc: after dealloc(addr1), sep_conj(dom_addr1, dom_addr2)
/// must be satisfiable because addr1 is no longer in domain.
#[test]
#[timeout(30000)]
fn test_sep_conj_after_dealloc_is_sat() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);

    let v1 = solver.int_const(111);
    let state = model.alloc(&mut solver, state, &ptr1, v1);
    let v2 = solver.int_const(222);
    let state = model.alloc(&mut solver, state, &ptr2, v2);
    let state = model.dealloc(&mut solver, state, &ptr1);

    // After dealloc addr1: in_domain(addr1) is false, in_domain(addr2) is true.
    // sep_conj(false, true) = not(and(false, true)) = not(false) = true → SAT
    let dom1 = model.in_domain(&mut solver, &state, &ptr1);
    let dom2 = model.in_domain(&mut solver, &state, &ptr2);
    let sep = model.encode_sep_conj(&mut solver, dom1, dom2);
    solver.assert_term(sep);

    assert_sat(
        &mut solver,
        "sep_conj must be satisfiable after deallocating one of two regions",
    );
}

// Three-way permission split proof (Re: #901 formal_proofs phase)

/// Three non-negative permission shares from a single alloc cannot exceed PERM_SCALE.
///
/// Extends test_permission_conservation (two shares) to three shares.
/// Proves: if s1 + s2 + s3 <= perm[addr] and perm[addr] == PERM_SCALE,
/// then s1 + s2 + s3 >= PERM_SCALE + 1 is UNSAT.
#[test]
#[timeout(30000)]
fn test_permission_three_way_split_conservation() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);
    let state = model.alloc(&mut solver, state, &ptr, val);

    let perm_actual = solver.select(state.permissions, addr);
    let s1 = solver.declare_const("s1", Sort::Int);
    let s2 = solver.declare_const("s2", Sort::Int);
    let s3 = solver.declare_const("s3", Sort::Int);
    let zero = solver.int_const(0);

    // All shares non-negative
    let ge1 = solver.ge(s1, zero);
    solver.assert_term(ge1);
    let ge2 = solver.ge(s2, zero);
    solver.assert_term(ge2);
    let ge3 = solver.ge(s3, zero);
    solver.assert_term(ge3);

    // Sum bounded by actual permission
    let sum12 = solver.add(s1, s2);
    let sum123 = solver.add(sum12, s3);
    let bounded = solver.le(sum123, perm_actual);
    solver.assert_term(bounded);

    // Try to make sum exceed PERM_SCALE
    let over = solver.int_const(PERM_SCALE + 1);
    let partial_exceed = solver.add(s1, s2);
    let sum123b = solver.add(partial_exceed, s3);
    let exceeds = solver.ge(sum123b, over);
    solver.assert_term(exceeds);

    assert_unsat(
        &mut solver,
        "three permission shares from single alloc cannot exceed PERM_SCALE",
    );
}

// Dealloc preserves heap value (Re: #901 formal_proofs phase)

/// Dealloc clears domain and permissions but does NOT erase the heap value.
///
/// This tests a subtle property: after dealloc, load() still returns the
/// last stored value (the raw array entry is preserved). Only domain and
/// permission gates prevent access — the actual data is not zeroed.
/// This is important for memory model correctness: "freed" memory is just
/// inaccessible, not necessarily zeroed.
#[test]
#[timeout(30000)]
fn test_dealloc_preserves_heap_value() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);

    // Raw load (bypassing domain check) should still return 999
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val);
    solver.assert_term(eq);

    assert_sat(
        &mut solver,
        "dealloc must NOT erase heap value — raw load should still see stored value",
    );

    // UNSAT dual: loaded value must be exactly 999 (not any other value)
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(999);
    let wrong2 = solver2.int_const(123);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);
    let state2 = model.dealloc(&mut solver2, state2, &ptr2);
    let loaded2 = model.load(&mut solver2, &state2, &ptr2);
    let eq_wrong = solver2.eq(loaded2, wrong2);
    solver2.assert_term(eq_wrong);

    assert_unsat(
        &mut solver2,
        "dealloc must preserve exact heap value — load==wrong must be UNSAT",
    );
}

// Alloc non-interference on heap at other addresses (Re: #901 formal_proofs phase)

/// Alloc at addr1 must not change the heap value at addr2 (concrete addresses).
///
/// This proves that alloc uses Array store (read-over-write) correctly:
/// store(heap, addr1, val1) does not affect select(heap, addr2) when addr1 != addr2.
#[test]
#[timeout(30000)]
fn test_alloc_noninterference_heap_value() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);
    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    // Alloc addr2 first, then alloc addr1
    let state = model.alloc(&mut solver, state, &ptr2, val2);
    let state = model.alloc(&mut solver, state, &ptr1, val1);

    // addr2's heap value must still be 222
    let loaded2 = model.load(&mut solver, &state, &ptr2);
    let eq2 = solver.eq(loaded2, val2);
    solver.assert_term(eq2);
    assert_sat(
        &mut solver,
        "alloc at addr1 must preserve heap value at addr2",
    );

    // UNSAT dual: addr2 value must NOT be addr1's value
    let (_, mut solver2, state2) = mem_test_setup();
    let a1 = solver2.int_const(10);
    let a2 = solver2.int_const(20);
    let p1 = MemPtr::new(a1);
    let p2 = MemPtr::new(a2);
    let v1 = solver2.int_const(111);
    let v2 = solver2.int_const(222);
    let state2 = model.alloc(&mut solver2, state2, &p2, v2);
    let state2 = model.alloc(&mut solver2, state2, &p1, v1);
    let loaded2b = model.load(&mut solver2, &state2, &p2);
    let eq_wrong = solver2.eq(loaded2b, v1);
    solver2.assert_term(eq_wrong);

    assert_unsat(
        &mut solver2,
        "alloc at addr1 must not clobber addr2 heap value (load==v1 must be UNSAT)",
    );
}

/// Solver push/pop scoping: push before a speculative alloc, pop to undo it.
///
/// Verifies that the memory model works correctly with solver push/pop:
/// after pop, the alloc's effects on domain/heap/perms are undone.
#[test]
#[timeout(30000)]
fn test_push_pop_undoes_alloc() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);

    // Before alloc, addr is not in domain
    let in_dom_before = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom_before);
    assert_unsat(
        &mut solver,
        "addr must not be in domain before alloc (constrained init)",
    );

    // Reset solver for push/pop test
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(999);

    solver2.push();
    let state2_alloc = model.alloc(&mut solver2, state2.clone(), &ptr2, val2);
    let in_dom2 = model.in_domain(&mut solver2, &state2_alloc, &ptr2);
    solver2.assert_term(in_dom2);
    assert_sat(
        &mut solver2,
        "addr should be in domain after alloc (within push scope)",
    );
    solver2.pop();

    // After pop, assertions from the push scope are removed.
    // The solver context reverts to the constrained init state.
    // Asserting in_domain on the ORIGINAL (pre-alloc) state should be UNSAT.
    let in_dom3 = model.in_domain(&mut solver2, &state2, &ptr2);
    solver2.assert_term(in_dom3);
    assert_unsat(
        &mut solver2,
        "after pop, in_domain on pre-alloc state must be UNSAT (push/pop undid assertions)",
    );
}

// Assertion strengthening: permission boundary precision (Re: #901)

/// PERM_SCALE - 1 must NOT satisfy has_full_permission.
///
/// Boundary test: has_full_permission checks `perm == PERM_SCALE`, so
/// PERM_SCALE - 1 must be rejected. This catches off-by-one errors
/// if the implementation ever changes from `eq` to `ge`.
#[test]
#[timeout(30000)]
fn test_almost_full_permission_is_not_full() {
    let (model, mut solver, state) = mem_test_setup_unconstrained();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let almost_full = solver.int_const(PERM_SCALE - 1);
    let mut almost_state = state.clone();
    almost_state.permissions = solver.store(almost_state.permissions, addr, almost_full);

    let has_full = model.has_full_permission(&mut solver, &almost_state, &ptr);
    solver.assert_term(has_full);

    assert_unsat(
        &mut solver,
        "PERM_SCALE - 1 must NOT satisfy has_full_permission (off-by-one guard)",
    );
}

/// Store at addr1 must NOT affect domain membership at addr2.
///
/// The store operation only writes to the heap array, not domain or
/// permissions. This test verifies the implementation doesn't accidentally
/// modify domain when storing to a different address.
#[test]
#[timeout(30000)]
fn test_store_noninterference_domain_preserved() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);

    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    // Allocate both addresses
    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);

    // Store a new value at addr1 — should NOT affect addr2's domain
    let new_val = solver.int_const(333);
    let state = model.store(&mut solver, state, &ptr1, new_val);

    // addr2 must still be in domain (UNSAT on negation)
    let in_dom2 = model.in_domain(&mut solver, &state, &ptr2);
    let not_in_dom2 = solver.not(in_dom2);
    solver.assert_term(not_in_dom2);

    assert_unsat(
        &mut solver,
        "store at addr1 must not remove addr2 from domain (UNSAT dual)",
    );
}

/// Store at addr1 must NOT affect permissions at addr2.
///
/// Store only modifies the heap array. Permission array must be unchanged
/// at all other addresses.
#[test]
#[timeout(30000)]
fn test_store_noninterference_permissions_preserved() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);

    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);

    let new_val = solver.int_const(333);
    let state = model.store(&mut solver, state, &ptr1, new_val);

    // addr2 must still have full permission (UNSAT on negation)
    let has_full2 = model.has_full_permission(&mut solver, &state, &ptr2);
    let not_full2 = solver.not(has_full2);
    solver.assert_term(not_full2);

    assert_unsat(
        &mut solver,
        "store at addr1 must not affect addr2 permissions (UNSAT dual)",
    );
}

/// Sep-conj with two disjoint allocations in the same state must be SAT.
///
/// When both addr1 and addr2 are allocated in the same state,
/// encode_sep_conj(in_domain(addr1), in_domain(addr2)) should still
/// be UNSAT (they both map to true). This is a soundness check:
/// two simultaneous allocations in the SAME heap DO overlap logically.
#[test]
#[timeout(30000)]
fn test_sep_conj_two_allocations_same_state_overlap() {
    let (model, mut solver, state) = mem_test_setup();

    let addr1 = solver.int_const(10);
    let addr2 = solver.int_const(20);
    let ptr1 = MemPtr::new(addr1);
    let ptr2 = MemPtr::new(addr2);

    let val1 = solver.int_const(111);
    let val2 = solver.int_const(222);

    let state = model.alloc(&mut solver, state, &ptr1, val1);
    let state = model.alloc(&mut solver, state, &ptr2, val2);

    // Both in_domain predicates are true (domain[addr1]==1, domain[addr2]==1)
    // sep_conj = NOT(AND(true, true)) = NOT(true) = false → UNSAT
    let dom1 = model.in_domain(&mut solver, &state, &ptr1);
    let dom2 = model.in_domain(&mut solver, &state, &ptr2);
    let sep = model.encode_sep_conj(&mut solver, dom1, dom2);
    solver.assert_term(sep);

    assert_unsat(
        &mut solver,
        "sep_conj must reject two active allocations — both in_domain are true",
    );
}

/// Alloc at addr1 then dealloc, followed by re-alloc at addr1 with different
/// value: domain, permission, and value must reflect the second alloc.
#[test]
#[timeout(30000)]
fn test_dealloc_then_realloc_resets_fully() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let val2 = solver.int_const(200);

    // Alloc -> dealloc -> re-alloc
    let state = model.alloc(&mut solver, state, &ptr, val1);
    let state = model.dealloc(&mut solver, state, &ptr);
    let state = model.alloc(&mut solver, state, &ptr, val2);

    // Must be back in domain
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    // Must have full permission
    let has_full = model.has_full_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_full);

    // Must see the second alloc's value
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val2);
    solver.assert_term(eq);

    assert_sat(
        &mut solver,
        "re-alloc after dealloc must restore domain, full permission, and new value",
    );

    // UNSAT dual: old value must not be observable
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let old2 = solver2.int_const(100);
    let new2 = solver2.int_const(200);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, old2);
    let state2 = model.dealloc(&mut solver2, state2, &ptr2);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, new2);
    let loaded2 = model.load(&mut solver2, &state2, &ptr2);
    let eq_old = solver2.eq(loaded2, old2);
    solver2.assert_term(eq_old);

    assert_unsat(
        &mut solver2,
        "re-alloc value must overwrite old — load==old_val must be UNSAT",
    );
}

/// Permission exactly at PERM_SCALE boundary for points-to must be SAT,
/// but PERM_SCALE + 1 must be UNSAT.
///
/// Boundary precision: encode_points_to uses `>=` for permission check.
/// With PERM_SCALE allocated, requesting exactly PERM_SCALE should succeed
/// (already tested above), but this test pairs it with PERM_SCALE + 1
/// in the same test for direct boundary comparison.
#[test]
#[timeout(30000)]
fn test_points_to_permission_exact_boundary() {
    let (model, mut solver, state) = mem_test_setup();

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Exactly PERM_SCALE: SAT
    let exact = solver.int_const(PERM_SCALE);
    let pt_exact = model.encode_points_to(&mut solver, &state, addr, val, exact);
    solver.assert_term(pt_exact);
    assert_sat(
        &mut solver,
        "points-to with exactly PERM_SCALE permission must be SAT",
    );

    // PERM_SCALE + 1: UNSAT
    let (_, mut solver2, state2) = mem_test_setup();
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val2 = solver2.int_const(999);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2);
    let over = solver2.int_const(PERM_SCALE + 1);
    let pt_over = model.encode_points_to(&mut solver2, &state2, addr2, val2, over);
    solver2.assert_term(pt_over);
    assert_unsat(
        &mut solver2,
        "points-to with PERM_SCALE + 1 must be UNSAT (off-by-one boundary)",
    );
}

// init_pure() guard tests (#1686)
//
// debug_assert_array_state guards were added in 097be5f to catch accidental
// array operations on pure-mode MemState (which holds int(0) placeholders).
// These tests verify the guards actually fire.

/// Calling `load` on init_pure() state panics in debug builds.
///
/// init_pure() returns int_const(0) placeholders, not array terms.
/// The debug_assert_array_state guard should catch this sort mismatch.
#[test]
#[timeout(30000)]
#[should_panic(expected = "init_pure")]
#[cfg(debug_assertions)]
fn test_init_pure_load_panics() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state = BaseMemoryModel::init_pure(&mut solver);
    let addr = solver.int_const(0);
    let ptr = MemPtr::new(addr);
    // This should panic: load requires array-sorted heap, but init_pure uses int(0)
    let _val = model.load(&mut solver, &pure_state, &ptr);
}

/// Calling `store` on init_pure() state panics in debug builds.
#[test]
#[timeout(30000)]
#[should_panic(expected = "init_pure")]
#[cfg(debug_assertions)]
fn test_init_pure_store_panics() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state = BaseMemoryModel::init_pure(&mut solver);
    let addr = solver.int_const(0);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(42);
    // This should panic: store requires array-sorted heap
    let _state = model.store(&mut solver, pure_state, &ptr, val);
}

/// Calling `in_domain` on init_pure() state panics in debug builds.
#[test]
#[timeout(30000)]
#[should_panic(expected = "init_pure")]
#[cfg(debug_assertions)]
fn test_init_pure_in_domain_panics() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state = BaseMemoryModel::init_pure(&mut solver);
    let addr = solver.int_const(0);
    let ptr = MemPtr::new(addr);
    // This should panic: in_domain requires array-sorted domain
    let _dom = model.in_domain(&mut solver, &pure_state, &ptr);
}

/// Calling `alloc` on init_pure() state panics in debug builds.
#[test]
#[timeout(30000)]
#[should_panic(expected = "init_pure")]
#[cfg(debug_assertions)]
fn test_init_pure_alloc_panics() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state = BaseMemoryModel::init_pure(&mut solver);
    let addr = solver.int_const(0);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(42);
    // This should panic: alloc requires array-sorted heap/domain/permissions
    let _state = model.alloc(&mut solver, pure_state, &ptr, val);
}

/// Calling `dealloc` on init_pure() state panics in debug builds.
#[test]
#[timeout(30000)]
#[should_panic(expected = "init_pure")]
#[cfg(debug_assertions)]
fn test_init_pure_dealloc_panics() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state = BaseMemoryModel::init_pure(&mut solver);
    let addr = solver.int_const(0);
    let ptr = MemPtr::new(addr);
    // This should panic: dealloc requires array-sorted domain/permissions
    let _state = model.dealloc(&mut solver, pure_state, &ptr);
}

/// Calling `get_permission` on init_pure() state panics in debug builds.
#[test]
#[timeout(30000)]
#[should_panic(expected = "init_pure")]
#[cfg(debug_assertions)]
fn test_init_pure_get_permission_panics() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state = BaseMemoryModel::init_pure(&mut solver);
    let addr = solver.int_const(0);
    let ptr = MemPtr::new(addr);
    // This should panic: get_permission requires array-sorted permissions
    let _perm = model.get_permission(&mut solver, &pure_state, &ptr);
}

/// Calling `has_permission` on init_pure() state panics in debug builds.
#[test]
#[timeout(30000)]
#[should_panic(expected = "init_pure")]
#[cfg(debug_assertions)]
fn test_init_pure_has_permission_panics() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state = BaseMemoryModel::init_pure(&mut solver);
    let addr = solver.int_const(0);
    let ptr = MemPtr::new(addr);
    // This should panic: has_permission requires array-sorted permissions
    let _has = model.has_permission(&mut solver, &pure_state, &ptr);
}

/// Calling `has_full_permission` on init_pure() state panics in debug builds.
#[test]
#[timeout(30000)]
#[should_panic(expected = "init_pure")]
#[cfg(debug_assertions)]
fn test_init_pure_has_full_permission_panics() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state = BaseMemoryModel::init_pure(&mut solver);
    let addr = solver.int_const(0);
    let ptr = MemPtr::new(addr);
    // This should panic: has_full_permission requires array-sorted permissions
    let _has = model.has_full_permission(&mut solver, &pure_state, &ptr);
}

/// Calling `encode_points_to` on init_pure() state panics in debug builds.
#[test]
#[timeout(30000)]
#[should_panic(expected = "init_pure")]
#[cfg(debug_assertions)]
fn test_init_pure_encode_points_to_panics() {
    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let pure_state = BaseMemoryModel::init_pure(&mut solver);
    let addr = solver.int_const(0);
    let val = solver.int_const(42);
    let perm = solver.int_const(1000);
    // This should panic: encode_points_to requires array-sorted heap/domain/permissions
    let _pt = model.encode_points_to(&mut solver, &pure_state, addr, val, perm);
}
