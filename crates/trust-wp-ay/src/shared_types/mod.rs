// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared types used across `encoder` and `verify` modules.
//!
//! Types that both modules need should live here to avoid bidirectional
//! coupling. Historically encoder imported types from verify; now both
//! import from this shared location. (#2655)

mod closure_compat;
mod provenance;
mod solve_types;

// Re-export closure compat types
#[cfg(test)]
pub(crate) use closure_compat::CaptureField;
pub(crate) use closure_compat::CaptureKind;
pub use closure_compat::ClosureCaptureInfo;
// Re-export provenance types
pub use provenance::VerificationProvenance;
// Re-export solve types used by encoder and verify
pub use solve_types::{
    proof_assert_native_replay_metadata, ProofAssertSliceCertificate, ProofAssertSliceDerivation,
    SolveEvidenceSnapshot, SolveLimitKindSnapshot, SolveResourceSnapshot, SolveStatisticsSnapshot,
    SolveVerificationLevelSnapshot, SolveVerificationSnapshot, StrictProofReplayObservation,
    UnknownReason,
};
