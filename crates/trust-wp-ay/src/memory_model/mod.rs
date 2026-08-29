// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Production usage: `BaseMemoryModel::init` and `init_pure` create the initial
// `MemState` in encoder constructors. After that handoff, production encoding
// stays on `AYEncoder`: mutable borrows go through `AYEncoder::encode_mut_borrow`
// (in `encoder/mut_borrow_enc.rs`). The experimental separation logic primitives
// (PointsTo, SepConj, MagicWand) live in `encoder/sep_logic.rs`, gated behind
// `#[cfg(any(test, feature = "sep-logic"))]`. The remaining trait methods (`load`,
// `store`, `alloc`, etc.) are reference implementations exercised only in unit
// tests.

//! Memory model types for separation logic encoding.
//!
//! # Production vs Test Usage
//!
//! **Production path** (encoder constructors):
//! - `BaseMemoryModel::init()` — creates initial `MemState` with symbolic arrays
//! - `BaseMemoryModel::init_pure()` — creates placeholder `MemState` for pure formulas
//!
//! **Test-only / reference path** (exercised in `base/tests.rs` and
//! `tests/memory_model_*.rs`):
//! - `load`, `store`, `alloc`, `dealloc` — heap operations
//! - `in_domain`, `get_permission`, `has_permission`, `has_full_permission`
//! - `encode_points_to`, `encode_sep_conj` — reference implementations that
//!   mirror the experimental encoder in `encoder/sep_logic.rs` (gated: `sep-logic`)
//!
//! The `AYEncoder` accesses `self.mem_state.{heap, domain, permissions}` directly
//! for runtime encoding. The trait methods exist to test memory-model semantics
//! in isolation and to keep a smaller reference implementation for targeted
//! array/permission tests.
//!
//! # Types
//!
//! - `MemState`: heap + domain + permissions arrays (used in production)
//! - `MemPtr`: abstract pointer (test-only; production uses raw `Term` addresses)
//! - `BaseMemoryModel`: the sole implementation
//!
//! Part of #274.

mod base;

#[cfg(test)]
use ay_dpll::api::Solver;
use ay_dpll::api::Term;
pub(crate) use base::BaseMemoryModel;

pub(crate) const LOG_TARGET: &str = "trust_wp_ay::memory_model";

/// Re-export the canonical permission scale from `trust_wp_core::formula::Permission`.
/// Used by `base.rs` (alloc, has_full_permission) and `encoder/heap.rs` (behind unsafe-heap).
#[cfg(any(test, feature = "unsafe-heap"))]
pub(crate) const PERM_SCALE: i64 = trust_wp_core::formula::Permission::PERM_SCALE;

/// Abstract pointer representation (test-only).
///
/// Not used in the production verification pipeline — `AYEncoder` operates on
/// raw `Term` addresses directly. Used in `BaseMemoryModel` trait methods and
/// their tests (`base/tests.rs`, `tests/memory_model_*.rs`).
///
/// For the base model, wraps a single address term.
/// The `meta` field supports wide pointers (size metadata) in tests.
#[cfg(test)]
#[derive(Clone, Debug)]
pub(super) struct MemPtr {
    /// Raw address component.
    pub(super) addr: Term,
    /// Optional metadata (size for wide pointers, etc.).
    pub(super) meta: Option<Term>,
}

#[cfg(test)]
impl MemPtr {
    /// Create a pointer from an address term.
    pub(super) fn new(addr: Term) -> Self {
        Self { addr, meta: None }
    }
}

/// Abstract memory state.
///
/// Holds the SMT terms representing heap contents, allocation domain,
/// and permission map.
#[derive(Clone, Debug)]
pub(crate) struct MemState {
    /// Heap contents: Array<Loc, Int>
    #[cfg_attr(not(test), allow(dead_code))]
    // accessed via self.heap in encoder/{heap,sep_logic}.rs
    pub(crate) heap: Term,
    /// Allocation domain: Array<Loc, Int> (1 = allocated, 0 = not; #1603)
    #[cfg_attr(not(test), allow(dead_code))]
    // accessed via self.domain in encoder/{heap,sep_logic}.rs
    pub(crate) domain: Term,
    /// Fractional permissions: Array<Loc, Int> (0..PERM_SCALE)
    #[cfg_attr(not(test), allow(dead_code))]
    // accessed via self.permissions in encoder/{heap,sep_logic}.rs
    pub(crate) permissions: Term,
}

impl MemState {
    /// Create a memory state with the three core arrays.
    pub(crate) fn new(heap: Term, domain: Term, permissions: Term) -> Self {
        Self {
            heap,
            domain,
            permissions,
        }
    }
}

/// Memory model abstraction used for initialization plus test/reference helpers.
///
/// # Production vs Test Usage
///
/// Only `init()` and `init_pure()` are called from production code (via
/// `encoder/constructors.rs`). All other methods (`load`, `store`, `alloc`,
/// `encode_points_to`, etc.) are exercised only through `BaseMemoryModel`
/// in unit tests. The production encoder does not dispatch through this trait;
/// it operates directly on `MemState` and `AYEncoder` helpers.
///
/// `encode_points_to` and `encode_sep_conj` are reference implementations —
/// the experimental versions live on `AYEncoder` in `encoder/sep_logic.rs`
/// (gated behind `cfg(any(test, feature = "sep-logic"))`) and differ (e.g.,
/// using the assertion pipeline for permission constraints).
///
/// # Design
///
/// The trait uses `&mut self` for `init` (which needs solver mutation).
/// `BaseMemoryModel` is the sole implementation.
#[cfg(test)]
pub(crate) trait MemoryModel {
    /// Load value from memory at pointer.
    fn load(&self, solver: &mut Solver, mem: &MemState, ptr: &MemPtr) -> Term;

    /// Store value to memory, returns updated state.
    fn store(&self, solver: &mut Solver, mem: MemState, ptr: &MemPtr, val: Term) -> MemState;

    /// Allocate location in domain with initial value and full permission.
    fn alloc(&self, solver: &mut Solver, mem: MemState, ptr: &MemPtr, val: Term) -> MemState;

    /// Deallocate location (remove from domain, zero permission).
    fn dealloc(&self, solver: &mut Solver, mem: MemState, ptr: &MemPtr) -> MemState;

    /// Check if location is in domain (returns Bool term: `domain[loc] == 1`).
    fn in_domain(&self, solver: &mut Solver, mem: &MemState, ptr: &MemPtr) -> Term;

    /// Get permission at location (returns Int term, 0..PERM_SCALE).
    fn get_permission(&self, solver: &mut Solver, mem: &MemState, ptr: &MemPtr) -> Term;

    /// Check if location has non-zero permission (returns Bool term).
    fn has_permission(&self, solver: &mut Solver, mem: &MemState, ptr: &MemPtr) -> Term;

    /// Check if location has full (PERM_SCALE) permission (returns Bool term).
    fn has_full_permission(&self, solver: &mut Solver, mem: &MemState, ptr: &MemPtr) -> Term;

    /// Reference/test-only encoding of a points-to assertion: `loc |-> val @ perm`.
    ///
    /// Returns a Bool term asserting:
    /// - loc is in domain
    /// - `heap\[loc\]` = val
    /// - `permissions\[loc\]` >= perm
    ///
    /// The experimental `AYEncoder::encode_points_to` in `encoder/sep_logic.rs`
    /// uses the assertion pipeline for permission bounds (gated: `sep-logic` feature).
    fn encode_points_to(
        &self,
        solver: &mut Solver,
        mem: &MemState,
        loc: Term,
        val: Term,
        perm: Term,
    ) -> Term;

    /// Reference/test-only encoding of separating conjunction.
    ///
    /// Takes two Bool terms representing domain membership at a single location
    /// and returns `!(left_domain && right_domain)`. This is a pointwise check —
    /// callers must apply it per-location or lift to quantified form.
    ///
    /// Note: `AYEncoder::encode_sep_conj` in `encoder/sep_logic.rs` (gated
    /// behind `sep-logic` feature) uses a different, formula-level approach
    /// with pairwise `l != r` or quantified disjointness. This trait method
    /// is a reference implementation exercised only in unit tests.
    fn encode_sep_conj(&self, solver: &mut Solver, left_domain: Term, right_domain: Term) -> Term;
}
