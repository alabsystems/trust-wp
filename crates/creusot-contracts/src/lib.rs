// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; these lints are not actionable for trust-wp's public surface.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unused_crate_dependencies,
    unreachable_pub
)]

//! Creusot compatibility shim for trust-wp.
//!
//! This crate re-exports trust-wp macros and types under the `creusot_contracts`
//! namespace, allowing Creusot test code to compile against trust-wp without
//! source modification.
//!
//! # Usage
//!
//! Creusot tests that use:
//! ```rust,ignore
//! use creusot_contracts::*;
//! ```
//! will get all trust-wp macros and trust-wp-std types via this shim.
//!
//! Part of #459 (Creusot compat shim).

// Make `trust_wp_std` available as an extern crate so that proc macro expansions
// using `::trust_wp_std::...` paths resolve correctly in downstream crates.
pub extern crate trust_wp_std;

// Re-export all proc macros and modules from trust-wp.
// Since trust-wp now re-exports trust-wp-std modules and prelude types,
// this gives us macros + Ghost, Snapshot, Int, Seq, spec traits, etc.
// Additional types not in the prelude (needed by Creusot compat tests)
pub use trust_wp::{
    bitwise_proof,
    builtin,
    check,
    ensures,
    erasure,
    extern_spec,
    ghost,
    ghost_let,
    invariant,
    law,
    logic,
    maintains,
    opaque,
    open_inv_result,
    pearlite,
    predicate,
    proof_assert,
    requires,
    // Modules (type namespace) — ghost, logic, invariant also come through above
    resolve,
    // macro_rules! macro
    seq,
    snapshot,
    terminates,
    trusted,
    variant,
    DeepModel,
    Default,
};
pub use trust_wp::{
    ghost::{
        invariant::{AtomicInvariant, AtomicInvariantSC, NonAtomicInvariant, Protocol},
        perm::Perm,
        resource::{Authority, Fragment, Resource},
    },
    logic::{dead, such_that, unreachable, Ag, Excl, Frac, Id, UnitRA, View, RA},
};
// Re-export prelude types at crate root (Ghost, Snapshot, Int, Seq, spec traits, etc.)
pub use trust_wp_std::prelude::*;

/// Prelude matching `creusot_contracts::prelude::*` (rare, but some tests use it).
pub mod prelude {
    pub use crate::*;
}
