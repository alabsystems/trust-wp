// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Thread-local state management for compilation sessions.
//!
//! Contains extraction-local caches used during MIR extraction and verification,
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

use crate::mir_analysis::extract::{
    clear_qualified_assoc_const_definitions, UNEVAL_CONST_EXPANSION_DEPTH,
};

mod mir_retention;
pub(crate) use mir_retention::{
    copy_mir_bodies, try_get_body_with_context, with_mir_session, RetainedBorrowckBody,
};

// Thread-local storage for discovered extern_spec! entries.
//
// These are discovered during after_expansion and used during mir_analysis
// for spec lookup. User-defined extern_specs take priority over std_specs.
// Cleared by `CacheGuard`; MIR retention has a separate TyCtxt-bound guard.
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
/// Thread-local caches (`EXTERN_SPECS`, `UNEVAL_CONST_EXPANSION_DEPTH`,
/// `QUALIFIED_ASSOC_CONST_DEFINITIONS`,
/// `result_protocol_state::FATAL_RESULT_COUNTERS`)
/// are **compilation-session scoped**, not process scoped.
/// They must be empty before any session begins and after every session ends,
/// regardless of how the session terminates (normal return, early error, panic).
///
/// `CacheGuard` enforces this: it clears on construction (entry) and on drop
/// (all exit paths including unwind). Manual calls remain safe but redundant.
pub(crate) fn clear_caches() {
    EXTERN_SPECS.with(|state| {
        state.borrow_mut().clear();
    });
    crate::result_protocol_state::clear_fatal_result_counters();
    UNEVAL_CONST_EXPANSION_DEPTH.with(|cell: &std::cell::Cell<usize>| {
        cell.set(0);
    });
    clear_qualified_assoc_const_definitions();
    super::clear_invariant_type_names();
    super::discovery::clear_callable_escape_cache();
    trust_wp_core::contract_parser::spelled_types::clear_shadowed_type_names();
    // The operator readings belong to one crate's type check (D-232).
    trust_wp_core::contract_parser::machine_arith::uninstall();
}

/// RAII guard that guarantees `clear_caches()` runs on all exit paths.
///
/// Created at the start of `after_expansion` to ensure thread-local caches
/// are cleared both on entry (defensive reset against stale data from a
/// previous session that exited abnormally) and on drop (covers normal
/// return, early return, and panic/unwind).
///
/// MIR retention is independently registered and released by `with_mir_session`;
/// clearing extraction-local state must not discard already captured MIR.
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
