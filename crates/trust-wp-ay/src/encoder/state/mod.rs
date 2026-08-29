// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Data-only state structs used by the AY encoder.
//!
//! These structs are pure state containers with no `AYEncoder` method
//! implementations. They are used across encoder submodules and extracted
//! here to keep `mod.rs` focused on core encoder logic.
//!
//! Extracted from `encoder/mod.rs` per design doc
//! `designs/2026-03-07-method-call-encoder-mod-decomposition.md` Step 1 and
//! split into subsystem-owned leaf modules per
//! `designs/2026-03-14-1584-encoder-state-module-decomposition.md`.

mod adt;
mod arithmetic_mode;
mod assertion_pipeline;
mod closure;
mod declarations;
mod dedup_snapshot;
mod encoding_cache;
mod quantifier;
#[cfg(any(test, feature = "sep-logic"))]
mod sep_logic;
mod seq;
mod sort_resolver;
mod traversal;

pub(crate) use adt::AdtState;
pub(crate) use arithmetic_mode::ArithmeticModeState;
pub(crate) use assertion_pipeline::{AssertionPhase, AssertionPipelineState};
pub(crate) use closure::ClosureState;
pub(crate) use declarations::DeclarationState;
pub(crate) use dedup_snapshot::DedupSnapshot;
pub(crate) use encoding_cache::EncodingCacheState;
pub(crate) use quantifier::QuantifierState;
#[cfg(test)]
pub(crate) use quantifier::SynthesizedTriggerDiagnostic;
#[cfg(any(test, feature = "sep-logic"))]
pub(crate) use sep_logic::{FormulaCacheKey, SepConjCache};
pub(crate) use seq::{
    ContainerElementInvariantSpec, ResolveElsewhereFootprint, ResolveElsewhereFrame, SeqFunctions,
    SeqState, SeqValue,
};
pub(crate) use sort_resolver::SortResolverState;
pub(crate) use traversal::TraversalState;

#[cfg(test)]
mod tests {
    use super::*;

    /// All state structs can be independently constructed and have empty defaults.
    /// This verifies the module re-exports are functioning and the structs are
    /// independently constructible without AYEncoder.

    #[test]
    fn test_declaration_state_constructible() {
        let state = DeclarationState::new();
        assert_eq!(state.logic_func_count(), 0);
        assert!(state.datatypes_is_empty());
    }

    #[test]
    fn test_seq_state_constructible() {
        let state = SeqState::new();
        assert!(state.funcs_is_none());
        assert_eq!(state.seq_values_len(), 0);
    }

    #[test]
    fn test_sort_resolver_state_constructible() {
        let state = SortResolverState::new();
        assert!(state.sort_hints_is_empty());
        assert!(state.view_identity_is_empty());
    }

    #[test]
    fn test_assertion_pipeline_state_constructible() {
        let state = AssertionPipelineState::new();
        assert!(!state.is_panicked());
        assert!(state.pending_assertions_is_empty());
    }

    #[test]
    fn test_closure_state_constructible() {
        let state = ClosureState::new();
        let _ = state;
    }

    #[test]
    fn test_adt_state_constructible() {
        let state = AdtState::new();
        let _ = state;
    }

    #[test]
    fn test_quantifier_state_constructible() {
        let state = QuantifierState::new();
        let _ = state;
    }

    #[test]
    fn test_arithmetic_mode_state_constructible() {
        let state = ArithmeticModeState::new();
        assert!(state.division_obligations().is_empty());
        assert!(!state.total_int_arithmetic());
        assert!(state.bitwise_proof_mode());
    }

    #[test]
    fn test_encoding_cache_state_constructible() {
        let state = EncodingCacheState::new();
        assert!(state.ext_eq_registry().is_empty());
        assert_eq!(state.ext_eq_registry_len(), 0);
        assert_eq!(state.fmap_len_proxy_count(), 0);
    }

    #[test]
    fn test_traversal_state_constructible() {
        let state = TraversalState::new();
        assert_eq!(state.recursion_depth, 0);
        assert!(state.path_conditions.is_empty());
    }
}
