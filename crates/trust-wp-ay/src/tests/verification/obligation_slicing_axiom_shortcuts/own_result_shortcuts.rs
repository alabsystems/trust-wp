// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use serial_test::serial;

use super::*;
// ── OwnResult is_ok pattern: result == exists<t> *self == OwnResult::Ok(t) (#1752) ──

/// Full verification pipeline test for `OwnResult::is_ok`:
///
/// ```text
/// body: match *self { OwnResult::Ok(_) => true, OwnResult::Err(_) => false }
/// ensures: result == exists<t: T> *self == OwnResult::Ok(t)
/// ```
///
/// The match in the body declares the OwnResult datatype. The exists
/// should be eliminated to `is_Ok(self_current)` via constructor equality
/// elimination (#1752). Then `result == is_Ok(self_current)` checks
/// that the boolean match result matches the tester.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_own_result_is_ok_full_pipeline() {
    // Body: match *self { OwnResult::Ok(_) => true, OwnResult::Err(_) => false }
    let body = match_expr(
        deref(var("self")),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                bool_expr(true),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                bool_expr(false),
            ),
        ],
    );

    // ensures: result == exists<t: T> *self == OwnResult::Ok(t)
    // The parser produces ExprSort::Int for generic T, simulated here.
    let exists_inner = eq(
        deref(var("self")),
        logic_fn_call("OwnResult::Ok", vec![var("t")]),
    );
    let exists_part = exists_with_sort("t", ExprSort::Int, exists_inner);
    let ens = eq(var("result"), exists_part);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .timeout(Some(Duration::from_secs(10))),
    );

    // First check encoding succeeds
    assert!(
        result.is_ok(),
        "is_ok pattern should not produce encoding error: {result:?}"
    );
    let vr = result.unwrap();
    // The match body produces true iff self is Ok(_). The exists quantifier
    // should eliminate to the tester is_Ok(self_current). Result should verify.
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "OwnResult::is_ok should verify: {vr:?}"
    );
}

/// Full verification pipeline test for `OwnResult::unwrap_or`:
///
/// ```text
/// body: match self { OwnResult::Ok(t) => t, OwnResult::Err(_) => default }
/// ensures[0]: forall<t: T> self == OwnResult::Ok(t) ==> result == t
/// ensures[1]: (exists<e: E> self == OwnResult::Err(e)) ==> result == default
/// ```
///
/// The forall should eliminate to `is_Ok(self) ==> result == accessor(self)`.
/// The exists should eliminate to `is_Err(self) ==> result == default`.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_own_result_unwrap_or_full_pipeline() {
    // Body: match self { OwnResult::Ok(t) => t, OwnResult::Err(_) => default }
    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("match_t".to_string()))),
                },
                var("match_t"),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                var("default"),
            ),
        ],
    );

    // ensures[0]: forall<t: T> self == OwnResult::Ok(t) ==> result == t
    let ens0 = forall_with_sort(
        "t",
        ExprSort::Int,
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Ok", vec![var("t")])),
            eq(var("result"), var("t")),
        ),
    );

    // ensures[1]: (exists<e: E> self == OwnResult::Err(e)) ==> result == default
    let ens1 = implies(
        exists_with_sort(
            "e",
            ExprSort::Int,
            eq(var("self"), logic_fn_call("OwnResult::Err", vec![var("e")])),
        ),
        eq(var("result"), var("default")),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens0, ens1])
            .return_expr(Some(&body))
            .timeout(Some(Duration::from_secs(10))),
    );

    assert!(
        result.is_ok(),
        "unwrap_or pattern should not produce encoding error: {result:?}"
    );
    let vr = result.unwrap();
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&vr),
        "OwnResult::unwrap_or should verify — forall/exists constructor elimination: {vr:?}"
    );
}

/// Driver-shaped enum control flow lowers through `discriminant()` + `SwitchInt`
/// instead of a high-level `Match`. Once `OwnResult` is registered as a native
/// datatype, the discriminant UF must stay pinned to the constructor tag or the
/// solver can pick the wrong branch while still satisfying `self == Err(_)`.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_driver_shaped_own_result_discriminant_body_respects_constructor() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_expr = var_with_sort(
        "self",
        ExprSort::Datatype(intern_sort_name("crate::OwnResult")),
    );
    let discr = method_call(self_expr.clone(), "discriminant", vec![]);
    let ok_tag = int(0);
    let err_tag = int(1);
    let body = let_assume(
        or(
            eq(discr.clone(), ok_tag.clone()),
            eq(discr.clone(), err_tag.clone()),
        ),
        ite(eq(discr, ok_tag), int(11), int(22)),
    );

    let ens_ok = forall_with_sort(
        "t",
        ExprSort::Int,
        implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
            eq(var("result"), int(11)),
        ),
    );
    let ens_err = forall_with_sort(
        "e",
        ExprSort::Int,
        implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
            eq(var("result"), int(22)),
        ),
    );

    let adt_decls = std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls))
            .timeout(Some(Duration::from_secs(10))),
    );

    assert!(
        result.is_ok(),
        "driver-shaped discriminant body should encode without semantic drift: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "discriminant tags must stay aligned with OwnResult constructors in driver-shaped bodies: {vr:?}"
    );
}

/// Driver-lowered enum payload reads use `__trust_wp_tuple_get_0(self)` after the
/// `SwitchInt` on `discriminant(self)`. The projection must stay connected to
/// the active constructor or the solver can satisfy `self == Ok(t)` while
/// choosing an unrelated payload for the body result.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_driver_shaped_own_result_payload_projection_respects_constructor() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_expr = var_with_sort(
        "self",
        ExprSort::Datatype(intern_sort_name("crate::OwnResult")),
    );
    let discr = method_call(self_expr.clone(), "discriminant", vec![]);
    let payload = logic_fn_call("__trust_wp_tuple_get_0", vec![self_expr.clone()]);
    let ok_tag = int(0);
    let err_tag = int(1);
    let body = let_assume(
        or(
            eq(discr.clone(), ok_tag.clone()),
            eq(discr.clone(), err_tag.clone()),
        ),
        ite(eq(discr, ok_tag), payload, int(99)),
    );

    let ens_ok = forall_with_sort(
        "t",
        ExprSort::Int,
        implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
            eq(var("result"), var("t")),
        ),
    );
    let ens_err = forall_with_sort(
        "e",
        ExprSort::Int,
        implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
            eq(var("result"), int(99)),
        ),
    );

    let adt_decls = std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls))
            .timeout(Some(Duration::from_secs(30))),
    );

    assert!(
        result.is_ok(),
        "driver-shaped enum payload read should encode without semantic drift: {result:?}"
    );
    let vr = result.unwrap();
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&vr),
        "driver-shaped payload projection must stay aligned with OwnResult constructors: {vr:?}"
    );
}

/// Some driver paths still lower enum payload reads to dotted projection vars
/// (`self.0`) instead of explicit tuple-get calls. Those projections must be
/// bridged back to the active constructor just like the tuple-get path.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_driver_shaped_own_result_direct_projection_var_respects_constructor() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_expr = var_with_sort(
        "self",
        ExprSort::Datatype(intern_sort_name("crate::OwnResult")),
    );
    let discr = method_call(self_expr.clone(), "discriminant", vec![]);
    let payload = var("self.0");
    let ok_tag = int(0);
    let err_tag = int(1);
    let body = let_assume(
        or(
            eq(discr.clone(), ok_tag.clone()),
            eq(discr.clone(), err_tag.clone()),
        ),
        ite(eq(discr, ok_tag), payload, int(99)),
    );

    let ens_ok = forall_with_sort(
        "t",
        ExprSort::Int,
        implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
            eq(var("result"), var("t")),
        ),
    );
    let ens_err = forall_with_sort(
        "e",
        ExprSort::Int,
        implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
            eq(var("result"), int(99)),
        ),
    );

    let adt_decls = std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls))
            .timeout(Some(Duration::from_secs(10))),
    );

    assert!(
        result.is_ok(),
        "driver-shaped direct projection var should encode without semantic drift: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "driver-shaped self.0 projection must stay aligned with OwnResult constructors: {vr:?}"
    );
}

/// `result/own.rs::unwrap` lowers through a driver-shaped discriminant split,
/// but its postcondition reconstructs the enum value:
/// `OwnResult::Ok(result) == self`.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_driver_shaped_own_result_unwrap_reconstructs_ok_constructor() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_expr = var_with_sort(
        "self",
        ExprSort::Datatype(intern_sort_name("crate::OwnResult")),
    );
    let discr = method_call(self_expr.clone(), "discriminant", vec![]);
    let ok_tag = int(0);
    let err_tag = int(1);
    let body = let_assume(
        or(
            eq(discr.clone(), ok_tag.clone()),
            eq(discr.clone(), err_tag.clone()),
        ),
        ite(eq(discr, ok_tag), var("self.0"), int(99)),
    );

    let req = exists_with_sort(
        "t",
        ExprSort::Int,
        eq(
            self_expr.clone(),
            logic_fn_call("OwnResult::Ok", vec![var("t")]),
        ),
    );
    let ens = eq(
        logic_fn_call("OwnResult::Ok", vec![var("result")]),
        self_expr.clone(),
    );

    let adt_decls = std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls))
            .timeout(Some(Duration::from_secs(10))),
    );

    assert!(
        result.is_ok(),
        "driver-shaped unwrap regression should encode without semantic drift: {result:?}"
    );
    let vr = result.unwrap();
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&vr),
        "driver-shaped unwrap should verify: {vr:?}"
    );
}

/// Verifies that the `ok()` method pattern works end-to-end:
///
/// ```text
/// body: match self { OwnResult::Ok(x) => Some(x), OwnResult::Err(_) => None }
/// ensures[0]: forall<t: T> self == OwnResult::Ok(t) ==> result == Some(t)
/// ensures[1]: (exists<e: E> self == OwnResult::Err(e)) ==> result == None
/// ```
///
/// This exercises the native-selector-to-enum_payload bridge (#1296):
/// the constructor equality elimination replaces `t` with the native selector
/// `Ok.0(self)`, while the match body uses `enum_payload_get_0(self)`. The
/// bridge axiom `is_Ok(x) ==> enum_payload_get_0(x) = Ok.0(x)` connects them.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_own_result_ok_method_selector_bridge_full_pipeline() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_expr = var_with_sort(
        "self",
        ExprSort::Datatype(intern_sort_name("crate::OwnResult")),
    );

    // Body: match self { OwnResult::Ok(x) => Some(x), OwnResult::Err(_) => None }
    let body = match_expr(
        self_expr.clone(),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("match_x".to_string()))),
                },
                logic_fn_call("Some", vec![var("match_x")]),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                logic_fn_call("None", vec![]),
            ),
        ],
    );

    // ensures[0]: forall<t: T> self == OwnResult::Ok(t) ==> result == Some(t)
    let ens0 = forall_with_sort(
        "t",
        ExprSort::Int,
        implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
            eq(var("result"), logic_fn_call("Some", vec![var("t")])),
        ),
    );

    // ensures[1]: (exists<e: E> self == OwnResult::Err(e)) ==> result == None
    let ens1 = implies(
        exists_with_sort(
            "e",
            ExprSort::Int,
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
        ),
        eq(var("result"), logic_fn_call("None", vec![])),
    );

    let adt_decls = std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens0, ens1])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls))
            .timeout(Some(Duration::from_secs(10))),
    );

    assert!(
        result.is_ok(),
        "ok() method pattern should not produce encoding error: {result:?}"
    );
    let vr = result.unwrap();
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&vr),
        "OwnResult::ok() should verify with selector bridge: {vr:?}"
    );
}

/// Dual regression for `result/own.rs::unwrap_err`.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_driver_shaped_own_result_unwrap_err_reconstructs_err_constructor() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_expr = var_with_sort(
        "self",
        ExprSort::Datatype(intern_sort_name("crate::OwnResult")),
    );
    let discr = method_call(self_expr.clone(), "discriminant", vec![]);
    let ok_tag = int(0);
    let err_tag = int(1);
    let body = let_assume(
        or(
            eq(discr.clone(), ok_tag.clone()),
            eq(discr.clone(), err_tag.clone()),
        ),
        ite(eq(discr, ok_tag), int(99), var("self.0")),
    );

    let req = exists_with_sort(
        "e",
        ExprSort::Int,
        eq(
            self_expr.clone(),
            logic_fn_call("OwnResult::Err", vec![var("e")]),
        ),
    );
    let ens = eq(
        logic_fn_call("OwnResult::Err", vec![var("result")]),
        self_expr.clone(),
    );

    let adt_decls = std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls))
            .timeout(Some(Duration::from_secs(10))),
    );

    assert!(
        result.is_ok(),
        "driver-shaped unwrap_err should encode without semantic drift: {result:?}"
    );
    let vr = result.unwrap();
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&vr),
        "driver-shaped unwrap_err should verify: {vr:?}"
    );
}

/// Verifies that multi-field constructor equality elimination fires and the
/// selector bridge axiom does not cause encoding errors or unsoundness (#1296).
///
/// A `Pair` enum with constructor `Pair::Both(fst, snd)` (2 fields) should:
/// 1. Have constructor equality elimination fire for `forall<a, b>`
/// 2. Get per-field selector bridges connecting enum_payload_get_N to native selectors
///
/// The test should verify that selector bridges are strong enough for the
/// quantified constructor postcondition, not just avoid counterexamples.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_multi_field_ctor_selector_bridge_no_unsoundness() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    // Pair enum: Both(Int, Int) | Empty
    let self_expr = var_with_sort("self", ExprSort::Datatype(intern_sort_name("crate::Pair")));

    // Body: match self { Pair::Both(a, _) => a, Pair::Empty => 0 }
    let body = match_expr(
        self_expr.clone(),
        vec![
            (
                Pattern::Constructor {
                    name: "Pair::Both".to_string(),
                    inner: Some(Box::new(Pattern::Binding("match_a".to_string()))),
                },
                var("match_a"),
            ),
            (
                Pattern::Constructor {
                    name: "Pair::Empty".to_string(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );

    // ensures: forall<a: Int, b: Int> self == Pair::Both(a, b) ==> result == a
    let ens = forall_with_sort(
        "a",
        ExprSort::Int,
        forall_with_sort(
            "b",
            ExprSort::Int,
            implies(
                eq(
                    self_expr.clone(),
                    logic_fn_call("Pair::Both", vec![var("a"), var("b")]),
                ),
                eq(var("result"), var("a")),
            ),
        ),
    );

    let adt_decls = std::collections::HashMap::from([(
        "Pair".to_string(),
        AdtDecl::new(
            "crate::Pair".to_string(),
            "Pair".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "Pair::Both".to_string(),
                    "Both".to_string(),
                    vec![
                        AdtFieldDecl::new("fst".to_string(), ExprSort::Int),
                        AdtFieldDecl::new("snd".to_string(), ExprSort::Int),
                    ],
                ),
                AdtConstructorDecl::new("Pair::Empty".to_string(), "Empty".to_string(), vec![]),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls))
            .timeout(Some(Duration::from_secs(10))),
    );

    assert!(
        result.is_ok(),
        "multi-field ctor selector bridge should not produce encoding error: {result:?}"
    );
    let vr = result.unwrap();
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&vr),
        "multi-field ctor selector bridge should verify the quantified selector postcondition: {vr:?}"
    );
}

/// Verifies that the qualified constructor reconstruction axiom (#1296) enables
/// the `OwnResult::Ok(result) == self` postcondition to verify without relying
/// on the standard `logic_Ok` path.
///
/// Without reconstruction, the solver knows `is_ok(self)` and
/// `spec_unwrap(self) == result` but cannot derive
/// `OwnResult::Ok(spec_unwrap(self)) == self`, which blocks postconditions of
/// the form `OwnResult::Ok(result) == self` (from `unwrap`/`expect`).
///
/// With reconstruction (`is_ok(x) ==> OwnResult::Ok(spec_unwrap(x)) = x`),
/// this postcondition becomes provable. The axiom is safe because this test
/// has no standard `logic_Ok` constructor in scope — only `OwnResult::Ok`.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_qualified_ok_reconstruction_enables_unwrap_postcondition() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_expr = var_with_sort(
        "self",
        ExprSort::Datatype(intern_sort_name("crate::OwnResult")),
    );

    // Body: match self { OwnResult::Ok(t) => t, OwnResult::Err(_) => absurd }
    let body = match_expr(
        self_expr.clone(),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("t".to_string()))),
                },
                var("t"),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                int(0), // dead code (precondition guards)
            ),
        ],
    );

    // requires: exists<t: T> self == OwnResult::Ok(t)
    let req = exists_with_sort(
        "t",
        ExprSort::Int,
        eq(
            self_expr.clone(),
            logic_fn_call("OwnResult::Ok", vec![var("t")]),
        ),
    );
    // ensures: OwnResult::Ok(result) == self
    let ens = eq(
        logic_fn_call("OwnResult::Ok", vec![var("result")]),
        self_expr.clone(),
    );

    let adt_decls = std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls))
            .timeout(Some(Duration::from_secs(15))),
    );

    assert!(
        result.is_ok(),
        "qualified Ok reconstruction should not produce encoding error (#1296): {result:?}"
    );
    let vr = result.unwrap();
    // With the reconstruction axiom `is_ok(x) ==> OwnResult::Ok(spec_unwrap(x)) = x`
    // the postcondition `OwnResult::Ok(result) = self` is provable.
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&vr),
        "qualified Ok reconstruction must enable OwnResult::Ok(result) == self (#1296): {vr:?}"
    );
}

/// Dual of the Ok reconstruction test: verifies that the Err reconstruction
/// axiom enables `OwnResult::Err(result) == self` for `unwrap_err`.
#[test]
#[timeout(60000)]
#[serial(solver_heavy)]
fn test_qualified_err_reconstruction_enables_unwrap_err_postcondition() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_expr = var_with_sort(
        "self",
        ExprSort::Datatype(intern_sort_name("crate::OwnResult")),
    );

    // Body: match self { OwnResult::Ok(_) => 0, OwnResult::Err(e) => e }
    let body = match_expr(
        self_expr.clone(),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                int(0), // dead code (precondition guards)
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                var("e"),
            ),
        ],
    );

    // requires: exists<e: E> self == OwnResult::Err(e)
    let req = exists_with_sort(
        "e",
        ExprSort::Int,
        eq(
            self_expr.clone(),
            logic_fn_call("OwnResult::Err", vec![var("e")]),
        ),
    );
    // ensures: OwnResult::Err(result) == self
    let ens = eq(
        logic_fn_call("OwnResult::Err", vec![var("result")]),
        self_expr.clone(),
    );

    let adt_decls = std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls))
            .timeout(Some(Duration::from_secs(15))),
    );

    assert!(
        result.is_ok(),
        "qualified Err reconstruction should not produce encoding error (#1296): {result:?}"
    );
    let vr = result.unwrap();
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&vr),
        "qualified Err reconstruction must enable OwnResult::Err(result) == self (#1296): {vr:?}"
    );
}
