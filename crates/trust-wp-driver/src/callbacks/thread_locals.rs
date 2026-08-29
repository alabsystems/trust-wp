// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Thread-local state management for compilation sessions.
//!
//! Contains all thread-local caches used during MIR extraction and verification,
//! plus the `CacheGuard` RAII type that ensures cleanup on all exit paths.
//!
//! # Lifecycle invariant (#1025)
//!
//! Thread-local caches are **compilation-session scoped**, not process scoped.
//! They must be empty before any session begins and after every session ends,
//! regardless of how the session terminates (normal return, early error, panic).
//! `CacheGuard` enforces this: it clears on construction (entry) and on drop
//! (all exit paths including unwind).

use std::{cell::RefCell, collections::HashMap};

use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

use crate::mir_analysis::extract::{
    clear_qualified_assoc_const_definitions, UNEVAL_CONST_EXPANSION_DEPTH,
};

// Thread-local storage for borrow-checked MIR bodies.
//
// The `mir_borrowck` query stores bodies here so we can access them
// during translation without re-running borrow checking.
thread_local! {
    pub(crate) static MIR_BODIES:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::new());
}

// Thread-local storage for discovered extern_spec! entries.
//
// These are discovered during after_expansion and used during mir_analysis
// for spec lookup. User-defined extern_specs take priority over std_specs.
// Same lifecycle invariant as MIR_BODIES; cleared by `CacheGuard`.
thread_local! {
    pub(crate) static EXTERN_SPECS:
        RefCell<HashMap<String, trust_wp_driver::StdSpec>> =
        RefCell::new(HashMap::new());
}

/// Clear all thread-local caches between compiler invocations.
///
/// This prevents stale entries from being observed when rustc_driver is
/// invoked multiple times in the same process (e.g., in test harnesses).
///
/// # Lifecycle invariant
///
/// Thread-local caches (`MIR_BODIES`, `EXTERN_SPECS`, `UNEVAL_CONST_EXPANSION_DEPTH`,
/// `QUALIFIED_ASSOC_CONST_DEFINITIONS`,
/// `result_protocol_state::FATAL_RESULT_COUNTERS`)
/// are **compilation-session scoped**, not process scoped.
/// They must be empty before any session begins and after every session ends,
/// regardless of how the session terminates (normal return, early error, panic).
///
/// `CacheGuard` enforces this: it clears on construction (entry) and on drop
/// (all exit paths including unwind). Manual calls remain safe but redundant.
pub(crate) fn clear_caches() {
    MIR_BODIES.with(|state| {
        state.borrow_mut().clear();
    });
    EXTERN_SPECS.with(|state| {
        state.borrow_mut().clear();
    });
    crate::result_protocol_state::clear_fatal_result_counters();
    UNEVAL_CONST_EXPANSION_DEPTH.with(|cell: &std::cell::Cell<usize>| {
        cell.set(0);
    });
    clear_qualified_assoc_const_definitions();
}

/// RAII guard that guarantees `clear_caches()` runs on all exit paths.
///
/// Created at the start of `after_expansion` to ensure thread-local caches
/// are cleared both on entry (defensive reset against stale data from a
/// previous session that exited abnormally) and on drop (covers normal
/// return, early return, and panic/unwind).
///
/// See issue #1025 for the soundness risk this addresses: the `MIR_BODIES`
/// cache uses `transmute` to extend MIR lifetimes to `'static`, which is
/// only sound within a single compilation session. Stale entries from a
/// prior session would alias freed `TyCtxt` arenas.
pub(crate) struct CacheGuard;

impl CacheGuard {
    /// Create a new guard, clearing all caches immediately (defensive entry reset).
    pub(crate) fn new() -> Self {
        clear_caches();
        CacheGuard
    }
}

impl Drop for CacheGuard {
    fn drop(&mut self) {
        clear_caches();
    }
}

/// Try to retrieve a MIR body from the thread-local cache with the correct lifetime.
///
/// # Safety
///
/// This function uses `transmute` to convert from `'static` to `'tcx`. This is safe
/// because:
/// 1. The MIR body is stored during `mir_borrowck` query execution
/// 2. The body actually lives for the duration of the compilation session
/// 3. The `'static` lifetime is used because thread-local storage requires it
/// 4. We only access this function during the same compilation session
/// 5. `CacheGuard` guarantees the cache is cleared at session boundaries,
///    preventing stale entries from leaking across sessions (#1025)
///
/// This pattern is used by Creusot and other rustc-based tools.
/// Reference: `reference/creusot/creusot/src/callbacks.rs:179-183`
pub(crate) fn try_get_body_with_context<'tcx>(
    def_id: LocalDefId,
) -> Option<&'tcx BodyWithBorrowckFacts<'tcx>> {
    MIR_BODIES.with(|state| {
        let map = state.borrow();
        map.get(&def_id).map(|body| {
            // SAFETY: The body lives for the duration of the compilation.
            // The 'static lifetime is a thread-local storage requirement,
            // not a true lifetime bound.
            // RISK: If rustc frees MIR bodies before verification completes,
            // these references become dangling. Relies on the invariant that
            // `get_bodies_with_borrowck_facts` data outlives all callbacks.
            // Creusot uses the identical pattern. (#1413)
            unsafe { std::mem::transmute(body) }
        })
    })
}

/// Copy borrow-checked MIR bodies into thread-local storage.
///
/// This follows the Creusot pattern of using `get_bodies_with_borrowck_facts`
/// to retrieve MIR with full borrow information.
pub(crate) fn copy_mir_bodies<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) {
    let opts = rustc_borrowck::consumers::ConsumerOptions::RegionInferenceContext;
    let bodies_with_facts =
        rustc_borrowck::consumers::get_bodies_with_borrowck_facts(tcx, def_id, opts);

    // SAFETY: The reader casts 'static back to 'tcx before using.
    // This is the same pattern used by Creusot.
    // RISK: Lifetime erasure assumes `bodies_with_facts` data remains valid for
    // the entire compilation session. If rustc changes to eagerly free these
    // bodies or reuse memory across compilation units, thread-local access
    // would produce UB. Creusot has the same risk profile. (#1413)
    let bodies_with_facts: FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>> =
        unsafe { std::mem::transmute(bodies_with_facts) };

    MIR_BODIES.with(|state| {
        let mut map = state.borrow_mut();
        for (def_id, body) in bodies_with_facts {
            // Don't replace existing entries (may be called multiple times)
            map.entry(def_id).or_insert(body);
        }
    });
}
