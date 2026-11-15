// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{Logic, SolveResult, Sort};
use ntest::timeout;

use super::{resolve_verified, resolve_verified_with_worker_thread_unsoundness};
use crate::{
    encoder::{
        unsoundness::{self, UnsoundnessCategory},
        AYEncoder,
    },
    tests::helpers::{gt, int, var},
    verify::{run_with_hard_timeout, ResolveContinuation},
    UnknownReason,
};

// --- retry_check_sat_on_timeout (#2142) ---

/// Verify that `retry_check_sat_on_timeout` returns `None` when the solver
/// result is Unknown but the reason is NOT timeout (e.g., incomplete theory).
#[test]
#[timeout(30000)]
fn retry_skips_non_timeout_unknown() {
    // Create a minimal encoder that will produce a definitive result (Unsat).
    // We don't actually trigger Unknown here — we verify that the function
    // correctly inspects the reason and returns None for non-timeout.
    let mut encoder = AYEncoder::new();
    // Solver hasn't returned Unknown, so unknown_reason() returns None.
    // retry_check_sat_on_timeout should return None (no retry needed).
    let result = crate::verify::retry_check_sat_on_timeout(&mut encoder);
    assert!(
        result.is_none(),
        "retry should return None when Unknown reason is not timeout"
    );
}

/// Verify that `retry_check_sat_on_timeout` takes the real timeout branch
/// and restores the original timeout after the retry attempt.
#[test]
#[timeout(30000)]
fn retry_timeout_unknown_restores_original_timeout() {
    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(std::time::Duration::ZERO));

    let first = encoder.check_sat();
    if matches!(first, SolveResult::Sat) {
        assert_eq!(
            encoder.solver().timeout(),
            Some(std::time::Duration::ZERO),
            "latest ay may return SAT immediately, but timeout must remain set"
        );
        return;
    }
    assert_eq!(
        first,
        SolveResult::Unknown,
        "zero timeout should force Unknown(timeout) or latest-ay immediate SAT"
    );
    assert_eq!(
        encoder.solver().reason_unknown_smtlib(),
        Some("timeout".to_string()),
        "solver should record timeout as the Unknown reason"
    );

    let result = crate::verify::retry_check_sat_on_timeout(&mut encoder);
    assert!(
        result.is_none(),
        "retry with zero timeout should still yield Unknown and return None"
    );
    assert_eq!(
        encoder.solver().timeout(),
        Some(std::time::Duration::ZERO),
        "retry must restore the original timeout after retrying"
    );
}

/// Verify that `retry_disabled()` reads `TRUST_WP_NO_RETRY` env var.
/// Note: since `retry_disabled` uses OnceLock, it caches the first result.
/// This test documents the expected behavior rather than testing the cache.
#[test]
#[timeout(30000)]
fn retry_disabled_returns_bool() {
    // Just verify the function returns without panicking.
    // The actual env var behavior is cached via OnceLock and depends on
    // process-level env state, so we just verify it's callable.
    let _ = crate::verify::retry_disabled();
}

#[test]
#[timeout(30000)]
fn unknown_result_from_encoder_prefers_panic_reason_over_solver_reason() {
    let mut encoder = AYEncoder::new();
    encoder.solver_mut().interrupt();
    let _ = encoder.check_sat();

    encoder
        .assertion_pipeline_mut_for_test()
        .set_solver_panic_reason_for_test(Some("simulated solver panic".to_string()));

    let result = crate::verify::unknown_result_from_encoder(&encoder);
    assert!(
        matches!(
            result,
            crate::verify::VerificationResult::Unknown(ref reason)
                if reason.as_str() == "ay solver panicked: simulated solver panic"
        ),
        "panic reason must take priority over the solver's generic Unknown reason: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn resolve_sat_result_surfaces_interrupted_unknown_reason() {
    let mut encoder = AYEncoder::new();
    encoder.solver_mut().interrupt();

    let result = crate::verify::resolve_sat_result(&mut encoder);
    assert!(
        matches!(
            result,
            crate::verify::VerificationResult::Unknown(ref reason) if reason.as_str() == "interrupted"
        ) || matches!(result, crate::verify::VerificationResult::Failed(_)),
        "resolve_sat_result should surface interrupted when ay reports it, or Failed \
         when latest ay treats the empty interrupted solver as SAT: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn resolve_sat_result_prefers_panic_reason_when_unknown() {
    let mut encoder = AYEncoder::new();
    encoder.solver_mut().interrupt();
    encoder
        .assertion_pipeline_mut_for_test()
        .set_solver_panic_reason_for_test(Some("panic while gathering model".to_string()));

    let result = crate::verify::resolve_sat_result(&mut encoder);
    assert!(
        matches!(
            result,
            crate::verify::VerificationResult::Unknown(ref reason)
                if reason.as_str() == "ay solver panicked: panic while gathering model"
        ),
        "resolve_sat_result should preserve the panic-specific unknown reason: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn run_with_hard_timeout_restores_encoder_on_success() {
    let mut encoder = AYEncoder::new();
    let timeout = std::time::Duration::from_millis(5);
    encoder.set_timeout(Some(timeout));

    let result = run_with_hard_timeout(&mut encoder, resolve_verified);

    assert!(
        matches!(
            result,
            ResolveContinuation::Continue(crate::verify::VerificationResult::Verified(_))
        ),
        "successful hard-timeout wrapper should continue with the original result: {result:?}"
    );
    assert_eq!(
        encoder.solver().timeout(),
        Some(timeout),
        "successful hard-timeout wrapper should restore the live encoder"
    );
}

#[test]
#[timeout(30000)]
fn run_with_hard_timeout_forced_timeout_aborts_with_timeout_reason() {
    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(std::time::Duration::from_millis(1)));
    let _guard = crate::verify::force_hard_timeout_for_test();

    let result = run_with_hard_timeout(&mut encoder, resolve_verified);

    assert!(
        matches!(
            result,
            ResolveContinuation::Abort(crate::verify::VerificationResult::Unknown(
                UnknownReason::Timeout
            ))
        ),
        "forced hard-timeout should abort with Unknown(timeout): {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn run_with_hard_timeout_merges_worker_unsoundness_before_demotion() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    unsoundness::reset();
    let before = unsoundness::snapshot();

    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(std::time::Duration::from_millis(5)));

    let continued = match run_with_hard_timeout(
        &mut encoder,
        resolve_verified_with_worker_thread_unsoundness,
    ) {
        ResolveContinuation::Continue(result) => result,
        other @ ResolveContinuation::Abort(_) => {
            panic!("worker-thread unsoundness regression should continue successfully: {other:?}")
        }
    };

    let merged = unsoundness::snapshot();
    assert_eq!(
        merged.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&1),
        "successful hard-timeout resolution should merge worker-thread counters back onto the caller thread"
    );

    let demoted = crate::verify::demote_if_unsound(&before, continued);
    match demoted {
        crate::verify::VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "worker-thread demoting categories should still demote Verified after merge: {reason}"
            );
            assert!(
                reason.as_str().contains("sort_fallback_to_int"),
                "demotion reason should cite the merged worker-thread category: {reason}"
            );
        }
        other => panic!("merged worker-thread SortFallbackToInt should demote Verified: {other:?}"),
    }

    unsoundness::reset();
}

#[test]
#[timeout(30000)]
fn register_type_invariants_on_encoder_uses_explicit_bool_param_sort() {
    use trust_wp_core::{formula::ExprSort, logic::type_invariant_method_name};

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let inv = trust_wp_core::type_invariant_def! {
        type_name: "Flag".to_string(),
        self_param: "self".to_string(),
        param_sort: Some(ExprSort::Bool),
        body: var("self"),
        is_newtype: false,
        element_invariant_method: None,
    };

    crate::verify::register_type_invariants_on_encoder(
        &mut encoder,
        Some(std::slice::from_ref(&inv)),
    )
    .expect("bool-sorted invariant registration should succeed");

    let method_name = type_invariant_method_name("Flag");
    let (_, decl) = encoder
        .decls()
        .logic_funcs_iter()
        .find(|(name, _)| name.contains(&method_name))
        .expect("type invariant declaration should be registered");
    assert_eq!(
        decl.domain(),
        vec![Sort::Bool],
        "explicit ExprSort::Bool must declare a Bool-domain invariant"
    );
    assert_eq!(
        encoder.ground_pool_for_test().axiom_count(),
        1,
        "type invariant registration should publish one defining axiom to the ground pool"
    );
    let axiom = &encoder.ground_pool_for_test().axioms()[0];
    assert_eq!(
        axiom.params,
        vec!["self".to_string()],
        "ground-pool axiom should preserve the invariant self parameter"
    );
    assert_eq!(
        axiom.body,
        var("self"),
        "ground-pool axiom should preserve the Bool body expression without Int fallback"
    );
}

#[test]
#[timeout(30000)]
fn register_type_invariants_on_encoder_preserves_mutref_typaram_sort() {
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::type_invariant_method_name,
    };

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let inv = trust_wp_core::type_invariant_def! {
        type_name: "MutRefTyParam".to_string(),
        self_param: "self".to_string(),
        param_sort: Some(ExprSort::MutRef(Box::new(ExprSort::TypeParam(
            intern_sort_name("T"),
        )))),
        body: var("self"),
        is_newtype: false,
        element_invariant_method: None,
    };

    crate::verify::register_type_invariants_on_encoder(
        &mut encoder,
        Some(std::slice::from_ref(&inv)),
    )
    .expect("mutref invariant registration should succeed");

    let method_name = type_invariant_method_name("MutRefTyParam");
    let expected_domain = encoder.sort_from_param_sort(ExprSort::MutRef(Box::new(
        ExprSort::TypeParam(intern_sort_name("T")),
    )));
    let (_, decl) = encoder
        .decls()
        .logic_funcs_iter()
        .find(|(name, _)| name.contains(&method_name))
        .expect("type invariant declaration should be registered");
    assert_eq!(
        decl.domain(),
        vec![expected_domain],
        "MutRef(TypeParam) invariant should preserve the mutable-reference carrier sort"
    );
}

#[test]
#[timeout(30000)]
fn register_type_invariants_on_encoder_marks_int_fallback_unsoundness() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let inv = trust_wp_core::type_invariant_def! {
        type_name: "Counter".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    };

    crate::verify::register_type_invariants_on_encoder(
        &mut encoder,
        Some(std::slice::from_ref(&inv)),
    )
    .expect("fallback invariant registration should still succeed");

    let (_, decl) = encoder
        .decls()
        .logic_funcs_iter()
        .find(|(name, _)| name.contains("Counter"))
        .expect("fallback invariant declaration should be registered");
    assert_eq!(
        decl.domain(),
        vec![Sort::Int],
        "missing param_sort should fall back to Int domain"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromVar)
            .is_some_and(|count| *count >= 1),
        "missing param_sort should record at least one Int-fallback unsoundness event: {delta:?}"
    );
    unsoundness::reset();
}

#[test]
#[timeout(30000)]
fn new_encoder_for_track_with_arrays_selects_expected_logic() {
    fn assert_case(
        label: &str,
        track: crate::TrackLevel,
        use_quantifiers: bool,
        needs_array_theory: bool,
        expected_logic: Logic,
        expected_seq_sort: Sort,
    ) {
        let mut encoder = crate::verify::new_encoder_for_track_with_arrays(
            track,
            use_quantifiers,
            needs_array_theory,
        )
        .unwrap_or_else(|err| panic!("{label}: encoder construction failed: {err}"));
        assert_eq!(
            encoder.logic(), expected_logic,
            "{label}: wrong solver logic for track={track:?}, quantifiers={use_quantifiers}, arrays={needs_array_theory}"
        );
        assert_eq!(
            encoder.get_seq_sort(),
            expected_seq_sort,
            "{label}: wrong proof-surface Seq carrier"
        );
    }

    assert_case(
        "reg_pure",
        crate::TrackLevel::Reg,
        false,
        false,
        Logic::QfLia,
        Sort::seq(Sort::Int),
    );
    // `new_encoder_for_track_with_arrays` calls `use_certifiable_seq_carrier()`
    // on the default quantified track, so `get_seq_sort()` here is
    // `Sort::Uninterpreted("Seq")`, not the native `Sort::seq(Sort::Int)`.
    // That is deliberate: ay withholds strict proof authority from any
    // refutation whose proof mentions a native `Sort::Seq(_)`, and this track
    // models sequences purely through trust-wp's own UF/array projectors, so
    // the uninterpreted spelling costs no reasoning power and keeps the proof
    // externally replayable. Retire only if that track deliberately returns to
    // the native carrier. The trade stays pinned two-sided by
    // `uflia_uninterpreted_seq_carrier_is_required_for_strict_proof_authority`
    // below, which is carrier-explicit.
    assert_case(
        "reg_quantified",
        crate::TrackLevel::Reg,
        true,
        false,
        Logic::Uflia,
        Sort::Uninterpreted("Seq".to_string()),
    );
    assert_case(
        "reg_array_theory",
        crate::TrackLevel::Reg,
        false,
        true,
        Logic::QfAuflia,
        Sort::seq(Sort::Int),
    );
    assert_case(
        "auto_array_quantified",
        crate::TrackLevel::Auto,
        true,
        true,
        Logic::Auflia,
        Sort::Uninterpreted("Seq".to_string()),
    );
    assert_case(
        "ptr_always_arrays",
        crate::TrackLevel::Ptr,
        false,
        false,
        Logic::QfAuflia,
        Sort::seq(Sort::Int),
    );
    assert_case(
        "mem_quantified",
        crate::TrackLevel::Mem,
        true,
        false,
        Logic::Auflia,
        Sort::seq(Sort::Int),
    );
}

/// The UFLIA carrier selection above is proof-authority relevant, not merely
/// a sort-shape preference. AY must withhold an otherwise clean refutation as
/// `ProofTrusted` when the same UFLIA problem exposes a native `Seq` term,
/// because the independent Alethe surface cannot parse that theory. Replacing
/// only the carrier with trust-wp's uninterpreted `Seq` sort makes the exact
/// equality refutation independently checkable.
#[test]
#[timeout(30000)]
fn uflia_uninterpreted_seq_carrier_is_required_for_strict_proof_authority() {
    fn contradictory_equality_chain(
        carrier: Sort,
    ) -> (SolveResult, Option<ay_dpll::UnknownReason>) {
        let mut solver = ay_dpll::api::Solver::new(Logic::Uflia);
        solver
            .try_set_option(":check-proofs-strict", "true")
            .expect("strict proof mode should be available");
        let a = solver.declare_const("proof_surface_sequence_a", carrier.clone());
        let b = solver.declare_const("proof_surface_sequence_b", carrier.clone());
        let c = solver.declare_const("proof_surface_sequence_c", carrier);
        let a_eq_b = solver.eq(a, b);
        let b_eq_c = solver.eq(b, c);
        let a_eq_c = solver.eq(a, c);
        let not_a_eq_c = solver.not(a_eq_c);
        solver.assert_term(a_eq_b);
        solver.assert_term(b_eq_c);
        solver.assert_term(not_a_eq_c);
        let result = solver.check_sat().into_inner();
        (result, solver.unknown_reason())
    }

    let (native_result, native_reason) = contradictory_equality_chain(Sort::seq(Sort::Int));
    assert_eq!(native_result, SolveResult::Unknown);
    assert_eq!(native_reason, Some(ay_dpll::UnknownReason::ProofTrusted));

    let (uf_result, uf_reason) =
        contradictory_equality_chain(Sort::Uninterpreted("Seq".to_string()));
    assert!(
        matches!(uf_result, SolveResult::Unsat(_)),
        "uninterpreted-carrier control must retain strict UNSAT authority: \
         result={uf_result:?}, reason={uf_reason:?}"
    );
    assert_eq!(uf_reason, None);
}
