// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; these lints are not actionable for trust-wp's public surface.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unused_crate_dependencies,
    unreachable_pub,
    // `tcx.get_all_attrs` is deprecated in favor of `find_attr!`, but trust-wp
    // reads CUSTOM proof-marker attributes (#[logic]/#[trusted]/...) that are
    // not parsed built-ins -- exactly the use the deprecation note sanctions.
    deprecated
)]
#![cfg_attr(test, allow(clippy::too_many_lines))]

//! trust-wp Driver - specification lookup library
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This library target exports specification lookup modules used by the
//! `trust-wp-rustc` binary during verification.
//!
//! # Public API surface
//!
//! The intended binary API consists of the flat re-exports below.
//! The `extern_specs` and `std_specs` modules are `pub(crate)` — internal
//! implementation details not exposed to external consumers (#1743).
//!
//! The verification pipeline itself (rustc callbacks, MIR extraction, contract
//! parsing, VC generation) lives in the `trust-wp-rustc` binary target
//! (`src/rustc_driver.rs`), not in this library.

pub(crate) mod extern_specs;
pub(crate) mod std_specs;

// --- Flat re-exports: binary API surface ---

pub use extern_specs::{
    builtin_trust_wp_std_specs, extern_specs_are_compatible, merge_local_extern_specs,
    normalize_extern_spec_path, parse_extern_spec_docs, ExternSpecEntry, ExternSpecMergeReport,
    ParseExternSpecError,
};
pub use std_specs::{
    builtin_clause_texts, lookup_extern_spec_only, lookup_spec_with_extern, StdSpec,
};
