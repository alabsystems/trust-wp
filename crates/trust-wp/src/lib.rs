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

//! trust-wp (Weakest Precondition) — Deductive verification for Rust
//!
//! trust-wp is a deductive verification tool for Rust. The **wp** suffix stands
//! for **Weakest Precondition**, referring to the Dijkstra-style WP calculus
//! used to prove program correctness.
//!
//! This is the primary user-facing crate for trust-wp verification.
//! It re-exports contract macros, compatibility markers, proof/ghost helpers,
//! and support items from `trust-wp-macros` and `trust-wp-std`, so
//! `use trust_wp::*;` provides the full verification facade:
//!
//! - **Core contracts:** `#[requires]`, `#[ensures]`, `#[invariant]`, `#[variant]`
//! - **Logic helpers:** `#[logic]`, `#[predicate]`, `#[law]`, `#[opaque]`
//! - **Compatibility markers:** `#[bitwise_proof]`, `#[builtin]`, `#[maintains]`, `#[trusted]`, `#[check]`, `#[erasure]`
//! - **Proof/ghost macros:** `ghost!`, `ghost_let!`, `snapshot!`, `proof_assert!`, `pearlite!`, `extern_spec!`, `seq!`
//! - **Support items:** `resolve`, `DeepModel`, `Clone`, `PartialEq`, `Default`
//!
//! See `contract-syntax.md` (repo root) for the detailed syntax reference. The native
//! facade surface is compile-checked in
//! `crates/trust-wp/tests/facade_direct_syntax.rs`,
//! `crates/trust-wp/tests/facade_ext_surface.rs`, and
//! `crates/trust-wp/tests/facade_trait_surface.rs` (`Clone` / `PartialEq`
//! resolution), while the underlying `trust_wp_std::prelude::*` surface is
//! compile-checked in `crates/trust-wp-std/tests/base_prelude_ext_surface.rs`
//! (helper-family `Ext` traits),
//! `crates/trust-wp-std/tests/prelude_trait_surface.rs` (`Clone` / `PartialEq`
//! resolution), and
//! `crates/trust-wp-std/tests/prelude_model_default_surface.rs` (`Default`
//! derive and `DeepModel` resolution).
//!
//! # Example
//!
//! ```rust,no_run
//! use trust_wp::*;
//!
//! #[requires(x > 0)]
//! #[ensures(result > x)]
//! fn increment(x: i32) -> i32 {
//!     ghost! {{
//!         let _debug = x + 1;
//!     }};
//!     x + 1
//! }
//!
//! #[requires(v.len() > 0)]
//! #[ensures(result == old(v.len()) - 1)]
//! fn pop_and_return_len(v: &mut Vec<i32>) -> usize {
//!     v.pop();
//!     v.len()
//! }
//! ```

// Make `trust_wp_std` available as an extern crate so proc macro expansions
// using `::trust_wp_std::...` paths resolve correctly in downstream crates.
pub extern crate trust_wp_std;

// --- Hidden internal macro (not re-exported by trust-wp-std) ---
#[doc(hidden)]
pub use trust_wp_macros::__trust_wp_trusted_proof_assert;
// --- Prelude types at crate root for `use trust_wp::*;` convenience ---
pub use trust_wp_std::prelude::*;
// --- Proc macros + modules from trust-wp-std ---
//
// `ghost`, `logic`, and `invariant` exist as both proc macros and modules
// in trust-wp-std. Importing them from a single source (trust-wp-std) brings
// both namespaces without conflict.
pub use trust_wp_std::{
    // Proc-macro-only re-exports
    bitwise_proof,
    builtin,
    check,
    ensures,
    erasure,
    extern_spec,
    // These names are both modules (type namespace) and proc macros (macro namespace)
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
    // Module-only re-exports
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

/// Prelude for convenient imports.
///
/// `use trust_wp::prelude::*;` is equivalent to `use trust_wp::*;` — both
/// provide all macros and specification types. The `prelude` module exists
/// for consistency with `trust_wp_std::prelude`.
pub mod prelude {
    pub use crate::*;
}
