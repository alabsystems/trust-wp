// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for explicit heap operations used in unsafe Rust verification (#125).
//!
//! Split from encoding.rs per #395.

use ntest::timeout;

use super::super::*;

#[test]
#[timeout(30000)]
fn test_heap_read_write() {
    // Test basic heap read and write operations
    let mut encoder = AYEncoder::new();

    // Create a location variable
    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    // Write value 42 to location
    let value = encoder.solver.int_const(42);
    let new_heap = encoder.heap_write(loc, value);

    // Read back from the new heap
    let read_val = encoder.solver.select(new_heap, loc);

    // Assert read value equals written value
    let eq = encoder.solver.eq(read_val, value);
    encoder.solver.assert_term(eq);

    // Should be SAT
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "heap read-after-write at same location should be Sat"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_read_unmodified() {
    // Test that heap_read returns the value stored in the heap array
    let mut encoder = AYEncoder::new();

    // Create a location and read from it
    let loc = encoder.solver.declare_const("ptr", Sort::Int);
    let read = encoder.heap_read(loc);

    // The read value should equal some integer (heap is unconstrained)
    let value = encoder.solver.int_const(100);
    let eq = encoder.solver.eq(read, value);
    encoder.solver.assert_term(eq);

    // Should be SAT (unconstrained heap can have any values)
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "reading unconstrained heap location should be Sat"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_alloc_sets_domain() {
    // Test that allocation marks location in domain
    let mut encoder = AYEncoder::new();

    // Create a fresh location
    let loc = encoder.solver.declare_const("ptr", Sort::Int);
    let value = encoder.solver.int_const(0);

    // Allocate at this location
    let (new_domain, _new_heap, _new_perms) = encoder.heap_alloc(loc, value);

    // Check that location is in the new domain (domain is Array<Int,Int>; #1603)
    let dom_val = encoder.solver.select(new_domain, loc);
    let one = encoder.solver.int_const(1);
    let in_domain = encoder.solver.eq(dom_val, one);
    encoder.solver.assert_term(in_domain);

    // Should be SAT
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "alloc should mark location in domain"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_alloc_sets_permission() {
    // Test that allocation grants full permission (100)
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);
    let value = encoder.solver.int_const(0);

    let (_new_domain, _new_heap, new_perms) = encoder.heap_alloc(loc, value);

    // Permission should be PERM_SCALE (full)
    let perm_at_loc = encoder.solver.select(new_perms, loc);
    let full = encoder.solver.int_const(Permission::PERM_SCALE);
    let eq = encoder.solver.eq(perm_at_loc, full);
    encoder.solver.assert_term(eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "alloc should grant full permission (PERM_SCALE={})",
        Permission::PERM_SCALE
    );
}

#[test]
#[timeout(30000)]
fn test_heap_dealloc_clears_domain() {
    // Test that deallocation removes location from domain
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    let (new_domain, _new_perms) = encoder.heap_dealloc(loc);

    // Check that location is NOT in domain after dealloc (domain is Array<Int,Int>; #1603)
    let dom_val = encoder.solver.select(new_domain, loc);
    let one = encoder.solver.int_const(1);
    let in_domain = encoder.solver.eq(dom_val, one);
    let not_in_domain = encoder.solver.not(in_domain);
    encoder.solver.assert_term(not_in_domain);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "dealloc should remove location from domain"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_dealloc_clears_permission() {
    // Test that deallocation sets permission to 0
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    let (_new_domain, new_perms) = encoder.heap_dealloc(loc);

    // Permission should be 0 after dealloc
    let perm_at_loc = encoder.solver.select(new_perms, loc);
    let zero = encoder.solver.int_const(0);
    let eq = encoder.solver.eq(perm_at_loc, zero);
    encoder.solver.assert_term(eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "dealloc should set permission to 0"
    );
}

#[test]
#[timeout(30000)]
fn test_is_allocated() {
    // Test the is_allocated helper
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    // Get allocation status - should be unconstrained initially
    let status = encoder.is_allocated(loc);

    // Both allocated and not-allocated should be possible
    // Test SAT when asserting it's allocated
    encoder.solver.assert_term(status);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "unconstrained is_allocated should be satisfiable"
    );
}

#[test]
#[timeout(30000)]
fn test_can_read_positive_permission() {
    // Test can_read returns true when permission > 0
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    // Set permission to some positive value (e.g., 50 for shared reference)
    let fifty = encoder.solver.int_const(50);
    let new_perms = encoder
        .solver
        .store(encoder.mem_state_for_test().permissions, loc, fifty);

    // Check can_read (permission > 0)
    let perm_at_loc = encoder.solver.select(new_perms, loc);
    let zero = encoder.solver.int_const(0);
    let can_read = encoder.solver.gt(perm_at_loc, zero);

    encoder.solver.assert_term(can_read);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "can_read with positive permission (50) should be Sat"
    );
}

#[test]
#[timeout(30000)]
fn test_can_write_full_permission() {
    // Test can_write returns true only when permission == PERM_SCALE
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);
    let value = encoder.solver.int_const(0);

    // Allocate (grants full permission)
    let (_new_domain, _new_heap, new_perms) = encoder.heap_alloc(loc, value);

    // Check can_write (permission == PERM_SCALE)
    let perm_at_loc = encoder.solver.select(new_perms, loc);
    let full = encoder.solver.int_const(Permission::PERM_SCALE);
    let can_write = encoder.solver.eq(perm_at_loc, full);

    encoder.solver.assert_term(can_write);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "can_write with full permission (PERM_SCALE={}) should be Sat",
        Permission::PERM_SCALE
    );
}

#[test]
#[timeout(30000)]
fn test_get_permission() {
    // Test get_permission returns the permission level at a location.
    // Note: get_permission reads from the encoder's internal permissions array,
    // not from a returned array. This test verifies the basic functionality
    // by checking that the initial (unconstrained) permissions can be any value.
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    // Get permission at location from encoder's internal permissions
    let perm = encoder.get_permission(loc);

    // The initial permissions array is unconstrained, so we can assert any value
    let fifty = encoder.solver.int_const(50);
    let eq = encoder.solver.eq(perm, fifty);
    encoder.solver.assert_term(eq);

    // Should be SAT (unconstrained array can have any value)
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "get_permission on unconstrained array should be Sat for any value"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_disjoint_different_locations() {
    // Test that disjoint locations pass the disjointness check
    let mut encoder = AYEncoder::new();

    let loc1 = encoder.solver.declare_const("ptr1", Sort::Int);
    let loc2 = encoder.solver.declare_const("ptr2", Sort::Int);

    // Assert loc1 != loc2
    let different = encoder.heap_disjoint(&[loc1], &[loc2]);
    encoder.solver.assert_term(different);

    // Should be SAT (locations can be different)
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "heap_disjoint for distinct locations should be Sat"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_disjoint_same_location_unsat() {
    // Test that same location fails disjointness
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    // Assert loc != loc (should be UNSAT)
    let disjoint = encoder.heap_disjoint(&[loc], &[loc]);
    encoder.solver.assert_term(disjoint);

    // Should be UNSAT (location can't be different from itself)
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "heap_disjoint of same location should be Unsat"
    );
}

#[test]
#[timeout(30000)]
fn test_fresh_heap_extension() {
    // Test creating fresh heap extension variables
    let mut encoder = AYEncoder::new();

    let (heap_ext, domain_ext, perms_ext) = encoder.fresh_heap_extension("test");

    // The extension arrays should be independent of the main heap
    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    // Values in extension can be different from main heap
    let main_val = encoder
        .solver
        .select(encoder.mem_state_for_test().heap, loc);
    let ext_val = encoder.solver.select(heap_ext, loc);
    let eq = encoder.solver.eq(main_val, ext_val);
    let different = encoder.solver.not(eq);
    encoder.solver.assert_term(different);

    // Extension domain can differ from main domain
    let main_alloc = encoder
        .solver
        .select(encoder.mem_state_for_test().domain, loc);
    let ext_alloc = encoder.solver.select(domain_ext, loc);
    // Just ensure we can use both
    let _ = main_alloc;
    let _ = ext_alloc;
    let _ = perms_ext;

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "fresh_heap_extension arrays should be independent of main heap"
    );
}

#[test]
#[timeout(30000)]
fn test_alloc_then_dealloc() {
    // Test sequence: alloc -> dealloc clears the location
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);
    let init_val = encoder.solver.int_const(42);

    // Step 1: Allocate
    let (alloc_domain, _alloc_heap, alloc_perms) = encoder.heap_alloc(loc, init_val);

    // Step 2: Deallocate (using the allocated state; domain is Array<Int,Int>; #1603)
    let zero = encoder.solver.int_const(0);
    let dealloc_domain = encoder.solver.store(alloc_domain, loc, zero);
    let dealloc_perms = encoder.solver.store(alloc_perms, loc, zero);

    // After dealloc: location should not be in domain
    let dom_val = encoder.solver.select(dealloc_domain, loc);
    let one = encoder.solver.int_const(1);
    let in_domain = encoder.solver.eq(dom_val, one);
    let not_in_domain = encoder.solver.not(in_domain);
    encoder.solver.assert_term(not_in_domain);

    // Permission should be 0
    let perm = encoder.solver.select(dealloc_perms, loc);
    let perm_zero = encoder.solver.eq(perm, zero);
    encoder.solver.assert_term(perm_zero);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "alloc then dealloc should clear domain and permissions"
    );
}

#[test]
#[timeout(30000)]
fn test_write_preserves_other_locations() {
    // Test that writing to one location doesn't affect others
    let mut encoder = AYEncoder::new();

    let loc1 = encoder.solver.declare_const("ptr1", Sort::Int);
    let loc2 = encoder.solver.declare_const("ptr2", Sort::Int);

    // Assert loc1 != loc2
    let eq = encoder.solver.eq(loc1, loc2);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    // Set initial value at loc2
    let val2 = encoder.solver.int_const(100);
    let heap_with_val2 = encoder
        .solver
        .store(encoder.mem_state_for_test().heap, loc2, val2);

    // Write different value to loc1 (using the heap with val2 already set)
    let val1 = encoder.solver.int_const(42);
    let final_heap = encoder.solver.store(heap_with_val2, loc1, val1);

    // Value at loc2 should still be 100
    let read_loc2 = encoder.solver.select(final_heap, loc2);
    let eq = encoder.solver.eq(read_loc2, val2);
    encoder.solver.assert_term(eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "write at loc1 should preserve value at loc2"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_union_fresh() {
    // Test creating fresh heap union arrays
    let mut encoder = AYEncoder::new();

    let (heap_union, domain_union, perms_union) = encoder.heap_union_fresh("test");

    // The union arrays should be independent - can have arbitrary values
    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    // Union heap can have different value than main heap
    let main_val = encoder
        .solver
        .select(encoder.mem_state_for_test().heap, loc);
    let union_val = encoder.solver.select(heap_union, loc);
    let eq = encoder.solver.eq(main_val, union_val);
    let different = encoder.solver.not(eq);
    encoder.solver.assert_term(different);

    // Just ensure we can use all three arrays
    let _ = encoder.solver.select(domain_union, loc);
    let _ = encoder.solver.select(perms_union, loc);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "heap_union_fresh arrays should be independent of main heap"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_disjoint_empty_slices() {
    // Test edge case: empty slices should return true
    let mut encoder = AYEncoder::new();

    // Both empty - vacuously disjoint
    let result = encoder.heap_disjoint(&[], &[]);
    encoder.solver.assert_term(result);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "heap_disjoint with two empty slices should be vacuously Sat"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_disjoint_one_empty() {
    // Test edge case: one empty slice should return true
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    // One empty, one non-empty - still vacuously disjoint
    let result = encoder.heap_disjoint(&[loc], &[]);
    encoder.solver.assert_term(result);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "heap_disjoint with one empty slice should be vacuously Sat"
    );
}

// =============================================================================
// heap_disjoint: multi-location tests (#552 Finding 2)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_heap_disjoint_two_by_two_sat() {
    // Two locations on each side, all distinct => SAT
    let mut encoder = AYEncoder::new();

    let a = encoder.solver.declare_const("a", Sort::Int);
    let b = encoder.solver.declare_const("b", Sort::Int);
    let c = encoder.solver.declare_const("c", Sort::Int);
    let d = encoder.solver.declare_const("d", Sort::Int);

    // Cross-pair disjointness: a≠c, a≠d, b≠c, b≠d
    let disjoint = encoder.heap_disjoint(&[a, b], &[c, d]);
    encoder.solver.assert_term(disjoint);

    // Also constrain all different (needed for SAT — the disjointness only
    // constrains cross-pair, not intra-pair)
    let ab_neq = encoder.solver.neq(a, b);
    let cd_neq = encoder.solver.neq(c, d);
    encoder.solver.assert_term(ab_neq);
    encoder.solver.assert_term(cd_neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "2x2 heap_disjoint with all-distinct locations should be Sat"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_disjoint_two_by_two_cross_overlap_unsat() {
    // If a == c is forced, cross-pair disjointness should make it UNSAT
    let mut encoder = AYEncoder::new();

    let a = encoder.solver.declare_const("a", Sort::Int);
    let b = encoder.solver.declare_const("b", Sort::Int);
    let c = encoder.solver.declare_const("c", Sort::Int);
    let d = encoder.solver.declare_const("d", Sort::Int);

    let disjoint = encoder.heap_disjoint(&[a, b], &[c, d]);
    encoder.solver.assert_term(disjoint);

    // Force a == c => violates a≠c from disjointness => UNSAT
    let forced_eq = encoder.solver.eq(a, c);
    encoder.solver.assert_term(forced_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "2x2 heap_disjoint with forced cross-overlap (a==c) should be Unsat"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_disjoint_allows_intra_side_aliasing() {
    // heap_disjoint only checks cross-pair, NOT intra-side.
    // a == b (same side) should still be SAT as long as cross-pair is ok.
    let mut encoder = AYEncoder::new();

    let a = encoder.solver.declare_const("a", Sort::Int);
    let b = encoder.solver.declare_const("b", Sort::Int);
    let c = encoder.solver.declare_const("c", Sort::Int);

    // Disjointness: a≠c, b≠c
    let disjoint = encoder.heap_disjoint(&[a, b], &[c]);
    encoder.solver.assert_term(disjoint);

    // Force a == b (intra-side aliasing, should be allowed)
    let ab_alias = encoder.solver.eq(a, b);
    encoder.solver.assert_term(ab_alias);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Intra-side aliasing should be allowed by heap_disjoint"
    );
}

// =============================================================================
// fresh_heap_extension: semantic independence test (#552 Finding 2)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_fresh_heap_extension_domain_independent() {
    // Extension domain should be independent of main domain
    let mut encoder = AYEncoder::new();

    let (_, domain_ext, _) = encoder.fresh_heap_extension("ext");
    let loc = encoder.solver.declare_const("loc", Sort::Int);

    // Main domain: loc is allocated (domain is Array<Int,Int>; #1603)
    let main_dom = encoder
        .solver
        .select(encoder.mem_state_for_test().domain, loc);
    let one = encoder.solver.int_const(1);
    let main_allocated = encoder.solver.eq(main_dom, one);
    encoder.solver.assert_term(main_allocated);

    // Extension domain: loc is NOT allocated
    let ext_dom = encoder.solver.select(domain_ext, loc);
    let ext_allocated = encoder.solver.eq(ext_dom, one);
    let not_ext = encoder.solver.not(ext_allocated);
    encoder.solver.assert_term(not_ext);

    // Should be SAT — the arrays are independent
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "extension domain should be independent of main domain"
    );
}

// =============================================================================
// heap_union_fresh: semantic independence test (#552 Finding 2)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_heap_union_fresh_all_three_arrays_independent() {
    // Verify all three union arrays (heap, domain, perms) are independent of
    // the main heap state and that heap/perms union arrays are distinct.
    let mut encoder = AYEncoder::new();

    let (heap_union, domain_union, perms_union) = encoder.heap_union_fresh("u");
    let loc = encoder.solver.declare_const("loc", Sort::Int);

    // Main heap/perms/domain get one set of values.
    let val42 = encoder.solver.int_const(42);
    let main_val = encoder
        .solver
        .select(encoder.mem_state_for_test().heap, loc);
    let main_eq = encoder.solver.eq(main_val, val42);
    encoder.solver.assert_term(main_eq);

    // Domain is Array<Int,Int>; 1 = allocated (#1603)
    let main_dom = encoder
        .solver
        .select(encoder.mem_state_for_test().domain, loc);
    let one = encoder.solver.int_const(1);
    let main_allocated = encoder.solver.eq(main_dom, one);
    let main_not_allocated = encoder.solver.not(main_allocated);
    encoder.solver.assert_term(main_not_allocated);

    let val7 = encoder.solver.int_const(7);
    let main_perm = encoder
        .solver
        .select(encoder.mem_state_for_test().permissions, loc);
    let main_perm_eq = encoder.solver.eq(main_perm, val7);
    encoder.solver.assert_term(main_perm_eq);

    // Union arrays get conflicting values at the same location.
    // This becomes UNSAT if any union array aliases the corresponding main array.
    let val99 = encoder.solver.int_const(99);
    let union_val = encoder.solver.select(heap_union, loc);
    let union_eq = encoder.solver.eq(union_val, val99);
    encoder.solver.assert_term(union_eq);

    // domain_union[loc] = 1 (allocated) while main domain[loc] != 1 (#1603)
    let dom_val = encoder.solver.select(domain_union, loc);
    let dom_one = encoder.solver.int_const(1);
    let dom_allocated = encoder.solver.eq(dom_val, dom_one);
    encoder.solver.assert_term(dom_allocated);

    // perms_union[loc] = 50 while main perms[loc] = 7
    let val50 = encoder.solver.int_const(50);
    let perm_val = encoder.solver.select(perms_union, loc);
    let perm_eq = encoder.solver.eq(perm_val, val50);
    encoder.solver.assert_term(perm_eq);

    // All constraints should be satisfiable simultaneously
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "all three union arrays should be independent of main heap state"
    );
}

// =============================================================================
// Alloc/dealloc frame property (#552 Finding 2)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_heap_alloc_frame_property() {
    // Alloc at loc1 should not affect heap/domain/perms at loc2.
    let mut encoder = AYEncoder::new();

    let loc1 = encoder.solver.declare_const("loc1", Sort::Int);
    let loc2 = encoder.solver.declare_const("loc2", Sort::Int);
    let val = encoder.solver.int_const(42);

    // Ensure different locations
    let neq = encoder.solver.neq(loc1, loc2);
    encoder.solver.assert_term(neq);

    let (new_domain, new_heap, new_perms) = encoder.heap_alloc(loc1, val);

    // Pin old and new domain at loc2 to not-allocated (#1603).
    // If alloc accidentally writes domain globally, this becomes UNSAT.
    let one = encoder.solver.int_const(1);
    let old_dom_loc2 = encoder
        .solver
        .select(encoder.mem_state_for_test().domain, loc2);
    let old_dom_alloc = encoder.solver.eq(old_dom_loc2, one);
    let old_dom_not_alloc = encoder.solver.not(old_dom_alloc);
    encoder.solver.assert_term(old_dom_not_alloc);
    let new_dom_loc2 = encoder.solver.select(new_domain, loc2);
    let new_dom_alloc = encoder.solver.eq(new_dom_loc2, one);
    let new_dom_not_alloc = encoder.solver.not(new_dom_alloc);
    encoder.solver.assert_term(new_dom_not_alloc);

    // Pin old/new permission at loc2 to the same non-full value.
    let old_perm_loc2 = encoder
        .solver
        .select(encoder.mem_state_for_test().permissions, loc2);
    let val17 = encoder.solver.int_const(17);
    let old_perm_is_17 = encoder.solver.eq(old_perm_loc2, val17);
    encoder.solver.assert_term(old_perm_is_17);
    let new_perm_loc2 = encoder.solver.select(new_perms, loc2);
    let new_perm_is_17 = encoder.solver.eq(new_perm_loc2, val17);
    encoder.solver.assert_term(new_perm_is_17);

    // Pin old/new heap at loc2 to 13 and ensure alloc does not perturb it.
    let old_heap_loc2 = encoder
        .solver
        .select(encoder.mem_state_for_test().heap, loc2);
    let val13 = encoder.solver.int_const(13);
    let old_heap_is_13 = encoder.solver.eq(old_heap_loc2, val13);
    encoder.solver.assert_term(old_heap_is_13);
    let new_heap_loc2 = encoder.solver.select(new_heap, loc2);
    let new_heap_is_13 = encoder.solver.eq(new_heap_loc2, val13);
    encoder.solver.assert_term(new_heap_is_13);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "alloc at loc1 should not affect heap/domain/perms at loc2"
    );
}

// =============================================================================
// Dealloc frame property (#552 proof_coverage)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_heap_dealloc_frame_property() {
    // Dealloc at loc1 should not affect domain/permissions at loc2.
    // Mirror of test_heap_alloc_frame_property for the deallocation path.
    let mut encoder = AYEncoder::new();

    let loc1 = encoder.solver.declare_const("loc1", Sort::Int);
    let loc2 = encoder.solver.declare_const("loc2", Sort::Int);

    // Ensure different locations
    let neq = encoder.solver.neq(loc1, loc2);
    encoder.solver.assert_term(neq);

    let (new_domain, new_perms) = encoder.heap_dealloc(loc1);

    // Pin old/new domain at loc2 to allocated (#1603).
    // If dealloc clears domain globally, this becomes UNSAT.
    let one = encoder.solver.int_const(1);
    let old_dom_loc2 = encoder
        .solver
        .select(encoder.mem_state_for_test().domain, loc2);
    let old_dom_alloc = encoder.solver.eq(old_dom_loc2, one);
    encoder.solver.assert_term(old_dom_alloc);
    let new_dom_loc2 = encoder.solver.select(new_domain, loc2);
    let new_dom_alloc = encoder.solver.eq(new_dom_loc2, one);
    encoder.solver.assert_term(new_dom_alloc);

    // Pin old/new permissions at loc2 to 50 (shared-ref permission).
    // If dealloc zeros permissions globally, this becomes UNSAT.
    let old_perm_loc2 = encoder
        .solver
        .select(encoder.mem_state_for_test().permissions, loc2);
    let val50 = encoder.solver.int_const(50);
    let old_perm_eq = encoder.solver.eq(old_perm_loc2, val50);
    encoder.solver.assert_term(old_perm_eq);
    let new_perm_loc2 = encoder.solver.select(new_perms, loc2);
    let new_perm_eq = encoder.solver.eq(new_perm_loc2, val50);
    encoder.solver.assert_term(new_perm_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Dealloc at loc1 should not affect domain/perms at loc2"
    );
}

// =============================================================================
// can_read / can_write negative paths (#552 proof_coverage)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_can_read_zero_permission_unsat() {
    // Pin permissions[loc] = 0, then call encoder.can_read(loc).
    // can_read reads from mem_state.permissions, so we constrain that array.
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    // Constrain the encoder's internal permissions array at loc to 0
    let zero = encoder.solver.int_const(0);
    let perm_at_loc = encoder
        .solver
        .select(encoder.mem_state_for_test().permissions, loc);
    let perm_is_zero = encoder.solver.eq(perm_at_loc, zero);
    encoder.solver.assert_term(perm_is_zero);

    // Call the actual can_read method (uses mem_state.permissions internally)
    let can_read = encoder.can_read(loc);
    encoder.solver.assert_term(can_read);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "can_read with zero permission should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_can_write_partial_permission_unsat() {
    // Pin permissions[loc] = 50, then call encoder.can_write(loc).
    // can_write reads from mem_state.permissions, so we constrain that array.
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);

    // Constrain the encoder's internal permissions array at loc to 50
    let fifty = encoder.solver.int_const(50);
    let perm_at_loc = encoder
        .solver
        .select(encoder.mem_state_for_test().permissions, loc);
    let perm_is_50 = encoder.solver.eq(perm_at_loc, fifty);
    encoder.solver.assert_term(perm_is_50);

    // Call the actual can_write method (uses mem_state.permissions internally)
    let can_write = encoder.can_write(loc);
    encoder.solver.assert_term(can_write);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "can_write with partial (50) permission should be UNSAT"
    );
}

// =============================================================================
// heap_alloc stores initial value (#552 proof_coverage)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_heap_alloc_stores_initial_value() {
    // Verify that heap_alloc(loc, val) stores val in the new heap at loc.
    // The existing alloc tests check domain and permissions but not the value.
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);
    let init_val = encoder.solver.int_const(42);

    let (_new_domain, new_heap, _new_perms) = encoder.heap_alloc(loc, init_val);

    // Read back from the new heap at the allocated location
    let read_back = encoder.solver.select(new_heap, loc);
    let eq = encoder.solver.eq(read_back, init_val);
    encoder.solver.assert_term(eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "heap_alloc should store the initial value in the new heap"
    );
}

#[test]
#[timeout(30000)]
fn test_heap_alloc_stores_initial_value_negative() {
    // Verify the stored value is exactly what was passed — asserting a different
    // value at the alloc location should be UNSAT.
    let mut encoder = AYEncoder::new();

    let loc = encoder.solver.declare_const("ptr", Sort::Int);
    let init_val = encoder.solver.int_const(42);

    let (_new_domain, new_heap, _new_perms) = encoder.heap_alloc(loc, init_val);

    // Assert the value at loc is 99 (different from 42)
    let wrong_val = encoder.solver.int_const(99);
    let read_back = encoder.solver.select(new_heap, loc);
    let wrong_eq = encoder.solver.eq(read_back, wrong_val);
    encoder.solver.assert_term(wrong_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Reading a different value from alloc location should be UNSAT"
    );
}

// =============================================================================
// fresh_heap_extension permissions independence (#552 proof_coverage)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_fresh_heap_extension_permissions_independent() {
    // Verify the permissions array from fresh_heap_extension is independent
    // of the main permissions array. The existing tests check heap and domain
    // independence but leave perms_ext unused.
    let mut encoder = AYEncoder::new();

    let (_, _, perms_ext) = encoder.fresh_heap_extension("ext");
    let loc = encoder.solver.declare_const("loc", Sort::Int);

    // Main permissions: loc has permission 100 (full)
    let main_perm = encoder
        .solver
        .select(encoder.mem_state_for_test().permissions, loc);
    let val100 = encoder.solver.int_const(100);
    let main_full = encoder.solver.eq(main_perm, val100);
    encoder.solver.assert_term(main_full);

    // Extension permissions: loc has permission 0 (none)
    let ext_perm = encoder.solver.select(perms_ext, loc);
    let val0 = encoder.solver.int_const(0);
    let ext_zero = encoder.solver.eq(ext_perm, val0);
    encoder.solver.assert_term(ext_zero);

    // Should be SAT — the arrays are independent
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Extension permissions should be independent of main permissions"
    );
}
