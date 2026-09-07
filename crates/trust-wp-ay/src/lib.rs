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
// HashMap is sufficient for internal API - don't need hasher generalization
#![allow(dead_code)]
#![allow(clippy::implicit_hasher)]
// Existing trust-wp-ay pedantic cleanup debt blocks broad `-D warnings`. Keep the
// debt explicit at the crate boundary so new non-listed warnings still surface.
#![allow(
    clippy::assertions_on_constants,
    clippy::bool_to_int_with_if,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::clone_on_copy,
    clippy::doc_lazy_continuation,
    clippy::doc_overindented_list_items,
    clippy::explicit_into_iter_loop,
    clippy::explicit_iter_loop,
    clippy::if_not_else,
    clippy::if_same_then_else,
    clippy::implicit_clone,
    clippy::int_plus_one,
    clippy::let_and_return,
    clippy::len_zero,
    clippy::manual_contains,
    clippy::manual_let_else,
    clippy::manual_strip,
    clippy::map_unwrap_or,
    clippy::match_like_matches_macro,
    clippy::match_wildcard_for_single_variants,
    clippy::needless_borrow,
    clippy::needless_continue,
    clippy::needless_lifetimes,
    clippy::needless_pass_by_value,
    clippy::needless_return,
    clippy::question_mark,
    clippy::redundant_closure,
    clippy::redundant_closure_for_method_calls,
    clippy::redundant_else,
    clippy::ref_as_ptr,
    clippy::similar_names,
    clippy::single_match_else,
    clippy::stable_sort_primitive,
    clippy::struct_excessive_bools,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::trivially_copy_pass_by_ref,
    clippy::type_complexity,
    clippy::unnecessary_fallible_conversions,
    clippy::unnecessary_lazy_evaluations,
    clippy::unnecessary_wraps,
    clippy::unnested_or_patterns,
    clippy::unused_self,
    clippy::used_underscore_binding,
    clippy::useless_conversion
)]
// ay-dpll deprecated panicking API methods in favor of try_* Result variants.
// Targeted #[allow(deprecated)] on specific modules that call the old API.
// ay solver internals use stack-allocated buffers that exceed the default 16KB
// threshold in test configurations. No file location is emitted by clippy.
#![cfg_attr(test, allow(clippy::large_stack_arrays))]

//! trust-wp AY - Verification condition encoding to ay SMT
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This crate translates verification conditions into ay SMT queries.
//! The primary encoding uses first-order logic with uninterpreted functions.
//!
//! # Encoding Strategy
//!
//! The production path uses FOL + uninterpreted functions on the ay API directly.
//! The experimental separation logic mode below is a reference encoding exercised
//! in unit tests (see `memory_model/mod.rs` for production vs test usage):
//!
//! 1. **Heap Model**: The heap is modeled as a partial function from
//!    locations to values. We use ay's array theory for this.
//!
//! 2. **Separation**: The separating conjunction P * Q is encoded by
//!    splitting the heap domain. Each formula operates on a disjoint
//!    portion of the heap.
//!
//! 3. **Permissions**: Fractional permissions are encoded as rational
//!    numbers attached to each points-to assertion.
//!
//! 4. **Magic Wand**: The magic wand P -* Q is encoded using auxiliary
//!    heap variables and implication.
//!
//! # SMT-LIB2 Serialization
//!
//! The `trust_wp_core::smt` module provides SMT-LIB2 serialization for
//! `--emit-smt` debugging output. All verification uses the direct ay API.

// Modules using ay-dpll deprecated panicking API get targeted allows.
// error, expr, expr_seq, logic, span, shared_types do NOT use deprecated API.
#[allow(deprecated)]
pub(crate) mod memory_model;
pub(crate) mod shared_types;

// The `internal-bench-api` feature re-exports `AYEncoder` from the crate root.
// Default bootstrap builds do not enable that feature, so the encoder's public
// methods look unreachable there even though opt-in benchmark users need them.
// Keep this scoped to the encoder module. (#1584)
#[cfg_attr(not(feature = "internal-bench-api"), allow(unreachable_pub))]
#[allow(deprecated)]
mod encoder;
mod error;
mod expr;
mod expr_seq;
mod logic;
mod source_symbol;
mod span;
#[allow(deprecated)]
mod verify;

// Check whether `TRUST_WP_DEBUG` is set in the environment.
//
// Cached via OnceLock internally (one env lookup per process).
// Lives at crate root so both `encoder` and `verify` can call it
// without creating a circular module dependency (#1654).
// Uses `ay_core::cached_env_flag!` (#1989).
ay_core::cached_env_flag!(pub(crate) trust_wp_debug_enabled, "TRUST_WP_DEBUG");

#[cfg(test)]
pub(crate) use ay_dpll::api::Sort;
#[cfg(test)]
#[allow(deprecated)]
pub(crate) use ay_dpll::api::{SolveResult, Solver, Term};
#[cfg(test)]
pub(crate) use trust_wp_core::{
    formula::{
        BinOp, ExprSort, Formula, Location, MatchArm, Pattern, Permission, PureExpr, UnOp, Value,
    },
    TrackLevel,
};

#[cfg(test)]
pub(crate) use crate::encoder::AYEncoder;
#[cfg(all(feature = "internal-bench-api", not(test)))]
#[doc(hidden)]
pub use crate::encoder::AYEncoder;
#[cfg(test)]
pub(crate) use crate::shared_types::{CaptureField, CaptureKind};
#[cfg(test)]
pub(crate) use crate::verify::verify_loop_invariant_positional;
#[cfg(test)]
pub(crate) use crate::verify::verify_preservation;
pub use crate::{
    encoder::{
        // #prophecy-slots (Fix B M1): the driver mints instantiation-aware
        // `Option<&mut T>` annotation names with this helper; the encoder
        // parses them back with the same grammar (sort_mapping.rs owns both
        // directions — no cross-crate grammar drift possible).
        // #prophecy-slots (Fix B M2): same contract for the carrier TUPLE
        // sort — the `Option<(&mut T, ..)>` sibling-binder shape.
        sort_context::sort_mapping::{
            mutref_carrier_tuple_sort_name, mutref_instantiated_option_name,
        },
        type_constants_for_int,
        unsoundness::{self, RiskLevel, UnsoundnessCategory},
    },
    error::EncodingError,
    // Kept public: the request builders and `closure_capture_info!` macro
    // still expose this type to external tests/consumers. (#1566, #2428)
    shared_types::{
        proof_assert_native_replay_metadata, ClosureCaptureInfo, ProofAssertSliceCertificate,
        ProofAssertSliceDerivation,
    },
    span::SourceSpan,
    verify::{
        proof_assert_obligation_slice_claims, proof_assert_obligation_slice_count,
        proof_assert_obligation_slice_derivations, structural_verified_outcome,
        verify_function_with_modes, verify_function_with_modes_outcome, verify_loop_invariant,
        verify_loop_invariant_outcome, verify_mut_borrow_function_with_modes,
        verify_mut_borrow_function_with_modes_outcome, BodyEffects, Counterexample,
        CounterexampleType, CounterexampleValue, LoopEncoderConfig, LoopVerificationContext,
        LoopVerificationOutcome, LoopVerificationResult, MutBorrowRequest, PostconditionInfo,
        ProofAssertModeGuard, ProofCertificateSummary, SolveEvidenceSnapshot,
        SolveLimitKindSnapshot, SolveResourceSnapshot, SolveStatisticsSnapshot,
        SolveVerificationLevelSnapshot, SolveVerificationSnapshot, StrictProofReplayObservation,
        UnknownReason, VarOrigin,
        VerificationOutcome, VerificationProvenance, VerificationRequest, VerificationResult,
    },
};

#[cfg(test)]
#[allow(deprecated)]
mod tests;
