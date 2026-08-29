// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Base memory model: array-based encoding with fractional permissions.
//!
//! The sole `MemoryModel` implementation. Production uses only `init()` and
//! `init_pure()` (called from `encoder/constructors.rs`) to seed
//! `AYEncoder::mem_state`. The encoding methods below are reference
//! implementations exercised by unit tests; production formulas are encoded by
//! `AYEncoder` in `encoder/sep_logic.rs`.
//!
//! Encoding:
//! - Heap: `Array<Int, Int>` (locations to values)
//! - Domain: `Array<Int, Int>` (allocated locations; 1 = allocated, 0 = not)
//! - Permissions: `Array<Int, Int>` (0..PERM_SCALE, see [`super::PERM_SCALE`])
//!
//! Domain uses Int (not Bool) because ay-dpll returns Unknown for
//! `select` on `Array(Int, Bool)` in QF_AUFLIA. See #1603.

#[cfg(test)]
use ay_dpll::api::Term;
use ay_dpll::api::{Solver, Sort};
use tracing::trace;

#[cfg(test)]
use super::{MemPtr, MemoryModel, PERM_SCALE};
use super::{MemState, LOG_TARGET};

/// Debug-only check that a `MemState`'s fields are array-sorted terms.
///
/// `init_pure()` returns `int_const(0)` placeholders for pure-only formulas.
/// Calling array operations (`select`, `store`) on those terms produces
/// ill-typed SMT queries. This guard catches accidental misuse during
/// development. (#1686)
#[cfg(test)]
fn debug_assert_array_state(solver: &Solver, mem: &MemState, op: &str) {
    debug_assert!(
        solver.get_sort(mem.heap).is_array(),
        "{op}: MemState.heap is {sort:?}, expected Array — was this state created by init_pure()?",
        sort = solver.get_sort(mem.heap),
    );
    debug_assert!(
        solver.get_sort(mem.domain).is_array(),
        "{op}: MemState.domain is {sort:?}, expected Array — was this state created by init_pure()?",
        sort = solver.get_sort(mem.domain),
    );
    debug_assert!(
        solver.get_sort(mem.permissions).is_array(),
        "{op}: MemState.permissions is {sort:?}, expected Array — was this state created by init_pure()?",
        sort = solver.get_sort(mem.permissions),
    );
}

/// Default array-based memory model with fractional permissions.
///
/// Encoding strategy:
/// - Heap: `Array<Int, Int>` maps locations to values
/// - Domain: `Array<Int, Int>` tracks allocated locations (1 = allocated, 0 = not)
/// - Permissions: `Array<Int, Int>` stores permission values (0..PERM_SCALE)
///
/// Domain uses `Array<Int, Int>` instead of `Array<Int, Bool>` because
/// ay-dpll returns `Unknown` for `select` on `Array(Int, Bool)` (#1603).
///
/// This model supports the core separation logic operations:
/// - Points-to: `loc |-> val @ perm`
/// - Separating conjunction via domain disjointness
/// - Fractional permission arithmetic
///
/// In production, these semantics are implemented on `AYEncoder`; this type is
/// retained as the reference/test harness implementation of the same model.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct BaseMemoryModel;

impl BaseMemoryModel {
    /// Create a new base memory model.
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self
    }

    /// Create initial memory state with fresh symbolic arrays.
    pub(crate) fn init(solver: &mut Solver) -> MemState {
        // All three arrays are intentionally unconstrained at init (#743).
        //
        // The production PointsTo encoding asserts points-to formulas on the
        // initial state WITHOUT calling alloc() first. If domain/permissions
        // are const_array(false)/const_array(0), then:
        //   select(const_array(false), loc) -> false  (at term construction time)
        // making ALL PointsTo formulas trivially UNSAT — a critical regression.
        //
        // Use `constrain_initial_state()` for contexts that need the
        // empty-domain invariant (e.g., memory safety verification).
        let heap = solver.declare_const("heap", Sort::array(Sort::Int, Sort::Int));
        let domain = solver.declare_const("domain", Sort::array(Sort::Int, Sort::Int));
        let permissions = solver.declare_const("perms", Sort::array(Sort::Int, Sort::Int));
        trace!(target: LOG_TARGET, "initializing symbolic memory state");

        MemState::new(heap, domain, permissions)
    }

    /// Create a "pure" memory state with placeholder Int terms.
    pub(crate) fn init_pure(solver: &mut Solver) -> MemState {
        let heap = solver.int_const(0);
        let domain = solver.int_const(0);
        let permissions = solver.int_const(0);
        trace!(target: LOG_TARGET, "initializing pure placeholder memory state");
        MemState::new(heap, domain, permissions)
    }

    /// Create the Int sort for locations.
    #[cfg(test)]
    pub(crate) fn loc_sort() -> Sort {
        Sort::Int
    }

    /// Create the Int sort for values.
    #[cfg(test)]
    pub(crate) fn val_sort() -> Sort {
        Sort::Int
    }

    /// Return a constrained copy of `mem` with empty domain and zero permissions.
    ///
    /// This replaces the symbolic domain/permissions arrays with `const_array`
    /// terms, enforcing the empty-domain invariant at the SMT term level.
    /// ay's read-over-const-array simplification (`select(const_array(v), i) → v`)
    /// works structurally at term construction time, avoiding the quantifier
    /// instantiation limitations that prevent assertion-based approaches from
    /// working in QfAuflia.
    ///
    /// Use this when the encoding pipeline requires that no location is initially
    /// allocated (e.g., separation logic encodings where allocation is explicit).
    /// Callers that need unconstrained initial arrays (e.g., for PointsTo encoding
    /// without prior alloc) should use `init()` directly.
    ///
    /// Part of #743.
    #[cfg(test)]
    pub(crate) fn constrain_initial_state(solver: &mut Solver, mem: &MemState) -> MemState {
        let zero = solver.int_const(0);
        let empty_domain = solver.const_array(Sort::Int, zero);
        let zero_perms = solver.const_array(Sort::Int, zero);
        MemState::new(mem.heap, empty_domain, zero_perms)
    }
}

#[cfg(test)]
impl MemoryModel for BaseMemoryModel {
    fn load(&self, solver: &mut Solver, mem: &MemState, ptr: &MemPtr) -> Term {
        debug_assert_array_state(solver, mem, "load");
        solver.select(mem.heap, ptr.addr)
    }

    fn store(&self, solver: &mut Solver, mut mem: MemState, ptr: &MemPtr, val: Term) -> MemState {
        debug_assert_array_state(solver, &mem, "store");
        mem.heap = solver.store(mem.heap, ptr.addr, val);
        mem
    }

    fn alloc(&self, solver: &mut Solver, mut mem: MemState, ptr: &MemPtr, val: Term) -> MemState {
        debug_assert_array_state(solver, &mem, "alloc");
        let one = solver.int_const(1);
        let full_perm = solver.int_const(PERM_SCALE);

        // Add to domain (1 = allocated)
        mem.domain = solver.store(mem.domain, ptr.addr, one);
        // Set heap value
        mem.heap = solver.store(mem.heap, ptr.addr, val);
        // Set full permission
        mem.permissions = solver.store(mem.permissions, ptr.addr, full_perm);

        mem
    }

    fn dealloc(&self, solver: &mut Solver, mut mem: MemState, ptr: &MemPtr) -> MemState {
        debug_assert_array_state(solver, &mem, "dealloc");
        let zero = solver.int_const(0);
        let zero_perm = solver.int_const(0);

        // Remove from domain (0 = deallocated)
        mem.domain = solver.store(mem.domain, ptr.addr, zero);
        // Zero permission
        mem.permissions = solver.store(mem.permissions, ptr.addr, zero_perm);

        mem
    }

    fn in_domain(&self, solver: &mut Solver, mem: &MemState, ptr: &MemPtr) -> Term {
        debug_assert_array_state(solver, mem, "in_domain");
        // Domain is Array<Int, Int> (not Bool) — ay-dpll bug #1603.
        // Return Bool term: domain[loc] == 1.
        let dom_val = solver.select(mem.domain, ptr.addr);
        let one = solver.int_const(1);
        solver.eq(dom_val, one)
    }

    fn get_permission(&self, solver: &mut Solver, mem: &MemState, ptr: &MemPtr) -> Term {
        debug_assert_array_state(solver, mem, "get_permission");
        solver.select(mem.permissions, ptr.addr)
    }

    fn has_permission(&self, solver: &mut Solver, mem: &MemState, ptr: &MemPtr) -> Term {
        debug_assert_array_state(solver, mem, "has_permission");
        let perm = solver.select(mem.permissions, ptr.addr);
        let zero = solver.int_const(0);
        solver.gt(perm, zero)
    }

    fn has_full_permission(&self, solver: &mut Solver, mem: &MemState, ptr: &MemPtr) -> Term {
        debug_assert_array_state(solver, mem, "has_full_permission");
        let perm = solver.select(mem.permissions, ptr.addr);
        let full = solver.int_const(PERM_SCALE);
        solver.eq(perm, full)
    }

    fn encode_points_to(
        &self,
        solver: &mut Solver,
        mem: &MemState,
        loc: Term,
        val: Term,
        perm: Term,
    ) -> Term {
        debug_assert_array_state(solver, mem, "encode_points_to");
        // loc |-> val @ perm means:
        // 1. loc is in domain
        // 2. heap[loc] = val
        // 3. permissions[loc] >= perm
        // 4. permissions[loc] <= PERM_SCALE (#1879)
        // 5. permissions[loc] >= 0 (#1879)

        // Domain is Array<Int, Int> (1 = allocated); convert to Bool (#1603)
        let dom_val = solver.select(mem.domain, loc);
        let one = solver.int_const(1);
        let in_dom = solver.eq(dom_val, one);
        let heap_val = solver.select(mem.heap, loc);
        let val_eq = solver.eq(heap_val, val);
        let current_perm = solver.select(mem.permissions, loc);
        let perm_ge = solver.ge(current_perm, perm);

        // Permission bounds (#1879)
        let perm_scale = solver.int_const(PERM_SCALE);
        let perm_bounded = solver.le(current_perm, perm_scale);
        let neg_one = solver.int_const(-1);
        let perm_non_neg = solver.gt(current_perm, neg_one);

        // in_dom && val_eq && perm_ge && perm_bounded && perm_non_neg
        let and1 = solver.and(in_dom, val_eq);
        let and2 = solver.and(and1, perm_ge);
        let and3 = solver.and(and2, perm_bounded);
        solver.and(and3, perm_non_neg)
    }

    fn encode_sep_conj(&self, solver: &mut Solver, left_domain: Term, right_domain: Term) -> Term {
        // Separation means: for all locations, not both in left and right domain
        // This is typically encoded at a higher level by the encoder using
        // domain predicates. For now, we just assert they're not both true
        // at any point where both are accessed.
        //
        // Note: Full quantified disjointness requires AUFLIA logic:
        // forall x. !(left_domain[x] && right_domain[x])
        //
        // For the QF case, we handle this at the formula level.
        let both = solver.and(left_domain, right_domain);
        solver.not(both)
    }
}

#[cfg(test)]
mod tests;
