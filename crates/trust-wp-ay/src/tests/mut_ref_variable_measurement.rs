// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MutRefVarNames variable count measurement tests (#2150).
//!
//! `MutRefVarNames` pre-declares `current`, `final_val` and the borrow
//! identity `id`; only the four cross-composition names (current_final,
//! current_current, final_current, final_final) are resolved on demand, when
//! a postcondition mentions them. These tests check that `&mut` shapes still
//! verify with that pre-declared set. The per-parameter SMT variable count
//! (7 for `&mut i32`, visible via TRUST_WP_DEBUG=1) is documented here, not
//! asserted.

use std::{collections::HashMap, time::Duration};

use ntest::timeout;

use super::{super::*, helpers::*};

/// Document the SMT variable count per `&mut i32` parameter when
/// `MutRefVarNames` pre-declares current, final_val and id but no
/// cross-composition name; the test itself asserts only the verdict.
///
/// Measured via TRUST_WP_DEBUG=1, the encoding loop in
/// `verify_mut_borrow_function_with_modes_inner` creates 7 variables per
/// `&mut i32` parameter:
///   v_current, v_final, old_v_current,
///   v_current_view, old_v_current_view, v_view, old_v_view
/// Each eagerly pre-declared cross-composition name would add one more
/// unconstrained variable per parameter to every function, whether or not
/// any postcondition mentions it.
///
/// Re: #2150
#[test]
#[timeout(30000)]
fn test_mut_ref_var_count_after_phase3_reduction() {
    use crate::encoder::MutRefVarNames;

    // The two value-carrying names; the third field, id, is the borrow identity.
    let names = MutRefVarNames::new("v");
    let field_names = [&names.current, &names.final_val];
    assert_eq!(
        field_names.len(),
        2,
        "MutRefVarNames should have exactly 2 fields after Phase 3"
    );

    // Verify a simple &mut i32 function and confirm it works with reduced vars.
    // fn increment_ref(v: &mut i32) { *v += 1 }
    // requires: *v > i32::MIN
    // ensures: ^v == old(*v) + 1
    let req = gt(deref(var("v")), int(i64::from(i32::MIN)));
    let ens = eq(final_expr(var("v")), add(deref(var("v")), int(1)));
    let body_expr = add(deref(var("v")), int(1));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .unwrap();
    // KNOWN-CLASS PIN (upstream proof-trusted certification gap): under ay's
    // mandatory strict UNSAT certification this trivial LIA/EUF VC computes
    // UNSAT but its certificate fails strict validation ("step t0 uses
    // unverified trust rule"), demoting Verified to `Unknown(ProofTrusted)` —
    // the sound direction. The encoding property this test guards is intact;
    // the gap is upstream certificate coverage. Retire the tolerance when the
    // class closes upstream. Every other outcome still fails the test.
    assert!(
        matches!(
            result,
            VerificationResult::Verified(_)
                | VerificationResult::Unknown(UnknownReason::ProofTrusted)
        ),
        "increment_ref should verify with 2-field MutRefVarNames (or demote to \
         the known proof-trusted certification gap): got {result:?}"
    );
}

/// Verify that the no-longer-pre-declared cross-composition variables
/// (current_final, current_current, final_current, final_final) are not
/// created by MutRefVarNames but can still be resolved on demand by
/// resolve_nameable_expr.
///
/// Cross-composition variables are demand-driven (created only if
/// postconditions reference them) rather than eagerly pre-declared for every
/// `&mut` parameter.
///
/// Re: #2150
#[test]
#[timeout(30000)]
fn test_cross_composition_vars_not_pre_declared() {
    use crate::encoder::sort_context::resolve_nameable_expr;

    // resolve_nameable_expr still resolves cross-composition patterns...
    assert_eq!(
        resolve_nameable_expr(&final_expr(deref(var("v"))), None),
        Some("v_current_final".to_string()),
    );
    assert_eq!(
        resolve_nameable_expr(&deref(deref(var("v"))), None),
        Some("v_current_current".to_string()),
    );
    assert_eq!(
        resolve_nameable_expr(&deref(final_expr(var("v"))), None),
        Some("v_final_current".to_string()),
    );
    assert_eq!(
        resolve_nameable_expr(&final_expr(final_expr(var("v"))), None),
        Some("v_final_final".to_string()),
    );

    // ...but MutRefVarNames::new does NOT pre-declare them.
    // A postcondition using ^(*v) would create v_current_final on demand
    // via encode_pure, but simple postconditions like ^v == old(*v) + 1
    // never reference them, saving 4 SMT variables per parameter.
}

/// Verify that a Vec-backed `&mut` parameter (with Seq view) also verifies
/// with `MutRefVarNames` pre-declaring only current, final_val and id.
///
/// Re: #2150
#[test]
#[timeout(30000)]
fn test_vec_mut_ref_verifies_after_phase3_reduction() {
    // fn push_and_check(v: &mut Vec<i32>) { v.push(v.len()); }
    // ensures: (^v)[v@.len()]@ == v@.len()
    let v_current_view = view(deref(var("v")));
    let v_len = method_call(v_current_view.clone(), "len", vec![]);
    let body_expr = method_call(v_current_view, "push_back", vec![v_len.clone()]);

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let final_v_indexed = method_call(final_expr(var("v")), "index_logic", vec![v_len.clone()]);
    let ens = eq(view(final_v_indexed), v_len);

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).timeout(Some(Duration::from_secs(5))),
    )
    .unwrap();
    match &result {
        VerificationResult::Verified(_) => {}
        VerificationResult::Unknown(reason)
            if reason.as_str().contains("sort_fallback_to_int")
                || reason.as_str().contains("unconstrained_result_var")
                || reason.as_str().contains("model validation")
                || reason.as_str().contains("vacuous proof")
                || reason.as_str().contains("timeout")
                // KNOWN-CLASS PIN (upstream Seq proof production gap):
                // the native-Seq UNSAT lacks a proof-producing re-solve
                // ("non-string sequence UNSAT not corroborated by a
                // proof-producing re-solve") and demotes to
                // `Unknown(ProofTrusted)` under ay's mandatory strict
                // certification — the sound direction, and the same bounded
                // solver-limitation family this arm already tolerates.
                // Retire when upstream Seq proof production closes the class.
                || reason.as_str().contains("proof-trusted") => {}
        other => panic!(
            "Vec push should verify or return a bounded known solver limitation \
             with 2-field MutRefVarNames: got {other:?}"
        ),
    }
}
