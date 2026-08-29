// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verification result types.
//!
//! This module re-exports the result types from `trust-wp-ay` and adds
//! convenience methods for common patterns in library consumers.
//!
//! The primary types are re-exported at the crate root:
//!
//! - [`VerificationResult`] — the main verification outcome
//! - [`Counterexample`] / [`CounterexampleValue`] — witness values on failure
//! - [`UnknownReason`] — typed reason for Unknown outcomes
//! - [`ProofCertificateSummary`] — proof quality metadata
//! - [`LoopVerificationResult`] — detailed loop verification result

// All result types are re-exported from lib.rs. This module exists
// as the organizational home for result-related documentation and
// any future convenience wrappers.

pub use trust_wp_ay::{
    Counterexample, CounterexampleType, CounterexampleValue, LoopVerificationResult,
    PostconditionInfo, ProofCertificateSummary, UnknownReason, VarOrigin, VerificationResult,
};
