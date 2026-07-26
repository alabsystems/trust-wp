// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; these lints are not actionable for trust-wp's public surface.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unused_crate_dependencies,
    unreachable_pub
)]

//! trust-wp Core - Contract/formula core and SMT output generation
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This crate contains:
//! - Separation logic AST definitions (`formula`)
//! - Contract expression parsing (`contract_parser`)
//! - Logic function and type invariant definitions (`logic`)
//! - SMT-LIB2 output generation (`smt`)

/// Contract expression parsing
pub mod contract_parser;

/// SMT-LIB2 output generation
pub mod smt;

/// Separation logic formula representation
pub mod formula;

/// Backend-neutral closure capture metadata
pub mod closure;

/// Logic function definitions
pub mod logic;

/// Structured verification result protocol for cross-process communication (#1690).
pub mod result_protocol;

/// Native request/result API for tRust-style bundle verification.
pub mod verify_bundle;

/// Shared tracing initialization (requires `tracing-init` feature).
#[cfg(feature = "tracing-init")]
pub mod tracing_init;

/// Memory tracking precision level for verification.
///
/// Controls how memory operations (loads/stores) are modeled in SMT.
/// Higher precision is more complete but slower.
///
/// Modeled after trust-mc's `--ay-chc-track` and `SeaHorn`'s `--track` flags.
/// See `designs/2026-02-02-precision-knobs.md` for design rationale.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum TrackLevel {
    /// Automatic track selection (default).
    /// Currently falls back to `Reg` behavior. MIR-based auto-detection is not yet implemented.
    #[default]
    Auto,
    /// Register-only: no heap operations, fastest.
    /// Loads return nondet values, stores are no-ops.
    /// Use for pure functions with no heap reasoning.
    Reg,
    /// Pointer validity: loads return nondet, but `in_domain` checks emitted.
    /// Detects invalid pointers without full memory semantics.
    Ptr,
    /// Full memory: array theory with select/store.
    /// Most precise, slowest. Required for heap-manipulating code.
    Mem,
}
