// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Heap operations for unsafe Rust encoding.
//!
//! These methods provide explicit heap-based encoding for unsafe Rust code
//! where Rust's ownership guarantees don't apply. They model:
//! - Heap reads: dereferencing raw pointers
//! - Heap writes: assigning through raw pointers
//! - Allocation: `Box::new`, malloc, etc.
//! - Deallocation: drop, free, etc.
//!
//! See: designs/2026-01-31-separation-logic-encoding.md Section 6

#[cfg(feature = "unsafe-heap")]
use ay_dpll::api::Sort;
#[cfg(any(test, feature = "sep-logic", feature = "unsafe-heap"))]
use ay_dpll::api::Term;
#[cfg(feature = "unsafe-heap")]
use tracing::{debug, trace};

use super::AYEncoder;
#[cfg(feature = "unsafe-heap")]
use crate::memory_model::{LOG_TARGET, PERM_SCALE};

impl AYEncoder {
    /// Encode a heap read operation: read value at location.
    ///
    /// This models `*ptr` for raw pointers in unsafe code.
    /// Returns the value stored at the location in the heap array.
    ///
    /// **Note:** This does NOT check allocation status or permissions.
    /// Use `is_allocated()` and `can_read()` separately to add those constraints
    /// when needed for verification conditions.
    ///
    /// # Contracts
    ///
    /// ```text
    /// REQUIRES: location is a well-formed Int term representing an address.
    /// ENSURES: Result = select(heap, location) - array read semantics.
    /// ENSURES: No side effects on encoder state beyond potential term caching.
    /// ```
    ///
    /// # Arguments
    /// * `location` - Term representing the memory address
    ///
    /// # Returns
    /// Term representing `heap[location]` (the value at that address)
    #[cfg(feature = "unsafe-heap")]
    pub(crate) fn heap_read(&mut self, location: Term) -> Term {
        trace!(target: LOG_TARGET, ?location, "heap read");
        self.solver.select(self.mem_state.heap, location)
    }

    /// Encode a heap write operation: update value at location.
    ///
    /// # Contracts
    ///
    /// ```text
    /// REQUIRES: location is a well-formed Int term (address).
    /// REQUIRES: value is a well-formed Int term.
    /// ENSURES: Result = store(self.mem_state.heap, location, value) - pure functional update.
    /// ENSURES: select(result, location) = value (write-read identity on returned heap).
    /// ENSURES: forall loc != location: select(result, loc) = select(heap, loc) (frame rule).
    /// ENSURES: self.mem_state is NOT modified (result is a new array term, not state update).
    /// ```
    ///
    /// This models `*ptr = val` for raw pointers in unsafe code.
    /// Returns a new heap array term with the updated value (functional style).
    ///
    /// # Arguments
    /// * `location` - Term representing the memory address
    /// * `value` - Term representing the value to write
    ///
    /// # Returns
    /// Term representing `store(heap, location, value)`
    #[cfg(feature = "unsafe-heap")]
    pub(crate) fn heap_write(&mut self, location: Term, value: Term) -> Term {
        debug!(target: LOG_TARGET, ?location, ?value, "heap write");
        self.solver.store(self.mem_state.heap, location, value)
    }

    /// Encode allocation: mark a location as allocated in the domain.
    ///
    /// # Contracts
    ///
    /// ```text
    /// REQUIRES: location is a well-formed Int term (fresh address).
    /// REQUIRES: value is a well-formed Int term (initial value).
    /// ENSURES: new_domain[location] = true (location now allocated).
    /// ENSURES: new_heap[location] = value (initial value stored).
    /// ENSURES: new_permissions[location] = PERM_SCALE (full ownership).
    /// ENSURES (Separation): Other locations unchanged in all arrays.
    /// ```
    ///
    /// This models `Arc::new(v)` or malloc in unsafe code.
    /// Returns constraints for:
    /// 1. Location added to domain
    /// 2. Value stored at location
    /// 3. Full permission granted
    ///
    /// # Arguments
    /// * `location` - Term representing the address to allocate
    /// * `value` - Term representing the initial value
    ///
    /// # Returns
    /// Tuple of (`new_domain`, `new_heap`, `new_permissions`)
    #[cfg(feature = "unsafe-heap")]
    pub(crate) fn heap_alloc(&mut self, location: Term, value: Term) -> (Term, Term, Term) {
        debug!(target: LOG_TARGET, ?location, ?value, "heap alloc");
        // Mark location as allocated (1 = allocated; domain is Int array, #1603)
        let one = self.solver.int_const(1);
        let new_domain = self.solver.store(self.mem_state.domain, location, one);
        // Store initial value
        let new_heap = self.solver.store(self.mem_state.heap, location, value);
        // Grant full permission
        let full_perm = self.solver.int_const(PERM_SCALE);
        let new_perms = self
            .solver
            .store(self.mem_state.permissions, location, full_perm);
        (new_domain, new_heap, new_perms)
    }

    /// Encode deallocation: remove a location from the domain.
    ///
    /// # Contracts
    ///
    /// ```text
    /// REQUIRES: location is a well-formed Int term (allocated address).
    /// REQUIRES: (Implicit) Caller must hold full permission to location.
    /// ENSURES: new_domain[location] = 0 (location deallocated).
    /// ENSURES: new_permissions[location] = 0 (no permission).
    /// ENSURES (Separation): Other locations unchanged in all arrays.
    /// ```
    ///
    /// This models `drop(Box::from_raw(ptr))` or free in unsafe code.
    /// Returns constraints for:
    /// 1. Location removed from domain
    /// 2. Permission set to zero
    ///
    /// # Arguments
    /// * `location` - Term representing the address to deallocate
    ///
    /// # Returns
    /// Tuple of (`new_domain`, `new_permissions`)
    #[cfg(feature = "unsafe-heap")]
    pub(crate) fn heap_dealloc(&mut self, location: Term) -> (Term, Term) {
        debug!(target: LOG_TARGET, ?location, "heap dealloc");
        // Mark location as deallocated (0 = deallocated; #1603)
        let zero = self.solver.int_const(0);
        let new_domain = self.solver.store(self.mem_state.domain, location, zero);
        // Remove permission
        let zero_perm = self.solver.int_const(0);
        let new_perms = self
            .solver
            .store(self.mem_state.permissions, location, zero_perm);
        (new_domain, new_perms)
    }

    /// Check if a location is allocated (in domain).
    ///
    /// # Arguments
    /// * `location` - Term representing the memory address
    ///
    /// # Returns
    /// Bool term: `domain[location] == 1` (domain is Int array; #1603)
    #[cfg(feature = "unsafe-heap")]
    pub(crate) fn is_allocated(&mut self, location: Term) -> Term {
        let dom_val = self.solver.select(self.mem_state.domain, location);
        let one = self.solver.int_const(1);
        self.eq_term(dom_val, one)
    }

    /// Get permission at a location.
    ///
    /// # Arguments
    /// * `location` - Term representing the memory address
    ///
    /// # Returns
    /// Term representing `permissions[location]` (integer 0..PERM_SCALE)
    #[cfg(feature = "unsafe-heap")]
    pub(crate) fn get_permission(&mut self, location: Term) -> Term {
        self.solver.select(self.mem_state.permissions, location)
    }

    /// Check if location has read permission (permission > 0).
    ///
    /// # Arguments
    /// * `location` - Term representing the memory address
    ///
    /// # Returns
    /// Term representing `permissions[location] > 0`
    #[cfg(feature = "unsafe-heap")]
    pub(crate) fn can_read(&mut self, location: Term) -> Term {
        let perm = self.solver.select(self.mem_state.permissions, location);
        let zero = self.solver.int_const(0);
        self.solver.gt(perm, zero)
    }

    /// Check if location has write permission (full permission = PERM_SCALE).
    ///
    /// # Arguments
    /// * `location` - Term representing the memory address
    ///
    /// # Returns
    /// Term representing `permissions[location] == PERM_SCALE`
    #[cfg(feature = "unsafe-heap")]
    pub(crate) fn can_write(&mut self, location: Term) -> Term {
        let perm = self.solver.select(self.mem_state.permissions, location);
        let full = self.solver.int_const(PERM_SCALE);
        self.eq_term(perm, full)
    }

    /// Encode heap disjointness constraint between two heap regions.
    ///
    /// For unsafe Rust with potential aliasing, we need explicit disjointness.
    /// This creates a constraint that all locations in locs1 are different
    /// from all locations in locs2.
    ///
    /// # Arguments
    /// * `locs1` - First set of location terms
    /// * `locs2` - Second set of location terms
    ///
    /// # Returns
    /// Conjunction of `l1 != l2` for all pairs.
    /// Returns `true` if either slice is empty (vacuously disjoint).
    ///
    /// # Edge Cases
    /// - Empty slices: Returns `true` (vacuous disjointness)
    /// - Same location in both: Returns UNSAT constraint
    #[cfg(any(test, feature = "sep-logic"))]
    pub(crate) fn heap_disjoint(&mut self, locs1: &[Term], locs2: &[Term]) -> Term {
        if locs1.is_empty() || locs2.is_empty() {
            return self.solver.bool_const(true);
        }
        // Build all pairwise neq constraints, then combine with and_many
        let mut constraints = Vec::with_capacity(locs1.len() * locs2.len());
        for l1 in locs1 {
            for l2 in locs2 {
                let neq = self.solver.neq(*l1, *l2);
                constraints.push(neq);
            }
        }
        self.solver.and_many(&constraints)
    }

    /// Create a symbolic heap union constraint.
    ///
    /// For magic wand encoding `Q(h ∪ h_ext)`, we need to model the union
    /// of two heaps. Since SMT arrays don't have a built-in union operation,
    /// we create a fresh result heap and constrain it to be the union.
    ///
    /// The union is defined as:
    /// - `domain_union[loc] = domain1[loc] ∨ domain2[loc]`
    /// - `heap_union[loc] = if domain1[loc] then heap1[loc] else heap2[loc]`
    /// - `perms_union[loc] = max(perms1[loc], perms2[loc])`
    ///
    /// **Note:** This returns fresh arrays representing the union. The caller
    /// must add constraints to enforce the union semantics using quantifiers
    /// or per-location constraints.
    ///
    /// # Arguments
    /// * `name_suffix` - Suffix for the result variable names
    ///
    /// # Returns
    /// Tuple of (`heap_union`, `domain_union`, `perms_union`) fresh arrays
    #[cfg(feature = "unsafe-heap")]
    pub(crate) fn heap_union_fresh(&mut self, name_suffix: &str) -> (Term, Term, Term) {
        let heap_union = self.solver.declare_const(
            &format!("heap_union_{name_suffix}"),
            Sort::array(Sort::Int, Sort::Int),
        );
        let domain_union = self.solver.declare_const(
            &format!("domain_union_{name_suffix}"),
            Sort::array(Sort::Int, Sort::Int),
        );
        let perms_union = self.solver.declare_const(
            &format!("perms_union_{name_suffix}"),
            Sort::array(Sort::Int, Sort::Int),
        );
        (heap_union, domain_union, perms_union)
    }

    /// Create a fresh heap variable for heap extension in magic wand encoding.
    ///
    /// Used for full heap-based magic wand encoding where we need:
    /// `∀ h_ext. (P(h_ext) ∧ disjoint(h, h_ext)) → Q(h ∪ h_ext)`
    ///
    /// # Arguments
    /// * `name_suffix` - Suffix for the variable name
    ///
    /// # Returns
    /// Tuple of (`heap_ext`, `domain_ext`, `perms_ext`) arrays
    #[cfg(feature = "unsafe-heap")]
    pub(crate) fn fresh_heap_extension(&mut self, name_suffix: &str) -> (Term, Term, Term) {
        let heap_ext = self.solver.declare_const(
            &format!("heap_{name_suffix}"),
            Sort::array(Sort::Int, Sort::Int),
        );
        let domain_ext = self.solver.declare_const(
            &format!("domain_{name_suffix}"),
            Sort::array(Sort::Int, Sort::Int),
        );
        let perms_ext = self.solver.declare_const(
            &format!("perms_{name_suffix}"),
            Sort::array(Sort::Int, Sort::Int),
        );
        (heap_ext, domain_ext, perms_ext)
    }
}
