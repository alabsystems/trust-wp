// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
// ── unwrap_or_default / as_ref / as_mut pipeline tests (#1296) ──────

/// Full verification pipeline for `OwnResult<T, E>::unwrap_or_default` where
/// the body uses a match expression and the postcondition uses quantified
/// constructor matching.
///
/// Models the compat shape:
/// ```text
/// #[ensures(forall<t: T> self == OwnResult::Ok(t) ==> result == t)]
/// #[ensures(forall<e: E> self == OwnResult::Err(e) ==> result == T::default())]
/// fn unwrap_or_default(self) -> T where T: Default
/// ```
///
/// Since we cannot model `T::default()` generically in the SMT encoding,
/// we model the simpler concrete case where the default is 0 (Int default).
/// This exercises the quantifier routing for constructor-matching postconditions
/// combined with the unwrap_or_default method dispatch. (#1296)
#[test]
#[timeout(30000)]
fn test_own_result_unwrap_or_default_pipeline_quantified_postcondition() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    // Body: match self { Ok(t) => t, Err(_) => 0 }
    let body = match_expr(
        var("self"),
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
                    inner: Some(Box::new(Pattern::Binding("_e".to_string()))),
                },
                int(0),
            ),
        ],
    );

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));

    // ensures: forall<t: T> self == Ok(t) ==> result == t
    let ens_ok = forall_with_sort(
        "t",
        t_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Ok", vec![var("t")])),
            eq(var("result"), var("t")),
        ),
    );
    // ensures: forall<e: E> self == Err(e) ==> result == 0
    let ens_err = forall_with_sort(
        "e",
        e_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Err", vec![var("e")])),
            eq(var("result"), int(0)),
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
                    vec![AdtFieldDecl::new("ok".to_string(), t_sort)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), e_sort)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "unwrap_or_default pipeline should encode without errors (#1296): {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "unwrap_or_default quantified postconditions should verify: \
         Ok(t) ==> result == t and Err(e) ==> result == 0 (#1296): {vr:?}"
    );
}

/// Full verification pipeline for `OwnResult<T, E>::as_ref` where
/// the body is identity (returns self) and the postcondition uses quantified
/// constructor matching.
///
/// In SMT, as_ref is identity (no ref/mut distinction). This test verifies
/// that the quantified postcondition `forall<t> self == Ok(t) ==> result == Ok(t)`
/// works through the full pipeline when the body is identity. (#1296)
#[test]
#[timeout(30000)]
fn test_own_result_as_ref_pipeline_quantified_postcondition() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    // Body: self (as_ref is identity in SMT)
    let body = var("self");

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));

    // ensures: forall<t: T> self == Ok(t) ==> result == Ok(t)
    let ens_ok = forall_with_sort(
        "t",
        t_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Ok", vec![var("t")])),
            eq(
                var("result"),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
        ),
    );
    // ensures: forall<e: E> self == Err(e) ==> result == Err(e)
    let ens_err = forall_with_sort(
        "e",
        e_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Err", vec![var("e")])),
            eq(
                var("result"),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
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
                    vec![AdtFieldDecl::new("ok".to_string(), t_sort)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), e_sort)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "as_ref pipeline should encode without errors (#1296): {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "as_ref identity body with quantified constructor postconditions should verify: \
         self == Ok(t) ==> result == Ok(t) is trivially true when result == self (#1296): {vr:?}"
    );
}

/// Minimal extracted-shape reduction for `OwnResult<T, E>::as_ref`.
///
/// The broad identity test above covers the pure semantic contract, but the
/// compat lowering matches on `*self` and reconstructs the enum branch-by-branch:
///
/// ```text
/// match *self {
///     OwnResult::Ok(t) => OwnResult::Ok(t),
///     OwnResult::Err(e) => OwnResult::Err(e),
/// }
/// ```
///
/// Pinning the deref-based shape separately from the identity test keeps a
/// regression in the compat lowering of `result/own.rs` distinguishable from
/// one in the pure contract.
#[test]
#[timeout(30000)]
fn test_own_result_as_ref_deref_match_identity_quantified_postcondition() {
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));

    let body = match_expr(
        deref(var("self")),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("t".to_string()))),
                },
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
        ],
    );

    let ens_ok = forall_with_sort(
        "t",
        t_sort.clone(),
        implies(
            eq(
                deref(var("self")),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
            eq(
                var("result"),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
        ),
    );
    let ens_err = forall_with_sort(
        "e",
        e_sort.clone(),
        implies(
            eq(
                deref(var("self")),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
            eq(
                var("result"),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
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
                    vec![AdtFieldDecl::new("ok".to_string(), t_sort)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), e_sort)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "as_ref deref-match reduction should encode without errors (#1296): {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "as_ref deref-match reduction should verify for the extracted compat shape (#1296): {vr:?}"
    );
}

/// Full verification pipeline for `OwnResult<T, E>::as_mut` modeled as
/// identity with quantified postconditions.
///
/// Like as_ref, as_mut is identity in the SMT encoding. This test uses
/// a match-based body (which is what the driver emits for as_mut) with
/// quantified postconditions. (#1296)
#[test]
#[timeout(30000)]
fn test_own_result_as_mut_pipeline_match_identity_quantified_postcondition() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    // Body: match self { Ok(t) => Ok(t), Err(e) => Err(e) }
    // This is the identity expressed as a match, which is what the driver emits.
    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("t".to_string()))),
                },
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
        ],
    );

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));

    // ensures: forall<t: T> self == Ok(t) ==> result == Ok(t)
    let ens_ok = forall_with_sort(
        "t",
        t_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Ok", vec![var("t")])),
            eq(
                var("result"),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
        ),
    );
    // ensures: forall<e: E> self == Err(e) ==> result == Err(e)
    let ens_err = forall_with_sort(
        "e",
        e_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Err", vec![var("e")])),
            eq(
                var("result"),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
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
                    vec![AdtFieldDecl::new("ok".to_string(), t_sort)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), e_sort)],
                ),
            ],
        ),
    )]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "as_mut match-identity pipeline should encode (#1296): {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "as_mut match-identity with quantified constructor postconditions should verify (#1296): {vr:?}"
    );
}

/// Verify that `unwrap_or_default` on Option (not Result) works through the
/// full pipeline with quantified postconditions.
///
/// Models: `fn unwrap_or_default(self) -> T`
/// ```text
/// #[ensures(forall<t: T> self == Some(t) ==> result == t)]
/// #[ensures(self == None ==> result == 0)]
/// ```
/// Uses the stdlib Option constructors (not OwnResult). (#1296)
#[test]
#[timeout(30000)]
fn test_option_unwrap_or_default_pipeline_quantified_postcondition() {
    // Body: match self { Some(t) => t, None => 0 }
    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("t".to_string()))),
                },
                var("t"),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );

    // ensures: forall<t> self == Some(t) ==> result == t
    let ens_some = forall(
        "t",
        implies(
            eq(var("self"), logic_fn_call("Some", vec![var("t")])),
            eq(var("result"), var("t")),
        ),
    );
    // ensures: self == None ==> result == 0
    let ens_none = implies(
        eq(var("self"), logic_fn_call("None", vec![])),
        eq(var("result"), int(0)),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_some, ens_none]).return_expr(Some(&body)),
    );

    assert!(
        result.is_ok(),
        "Option unwrap_or_default pipeline should encode (#1296): {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "Option unwrap_or_default with quantified postcondition should verify: \
         Some(t) ==> result == t and None ==> result == 0 (#1296): {vr:?}"
    );
}

/// Verify that `as_ref` on Option works through the full pipeline when
/// modeled as identity with quantified postconditions.
///
/// Models: `fn as_ref(&self) -> Option<&T>`
/// In SMT: identity, so `result == self`.
/// ```text
/// #[ensures(forall<t> self == Some(t) ==> result == Some(t))]
/// #[ensures(self == None ==> result == None)]
/// ```
#[test]
#[timeout(30000)]
fn test_option_as_ref_pipeline_quantified_postcondition() {
    // Body: self (identity)
    let body = var("self");

    // ensures: forall<t> self == Some(t) ==> result == Some(t)
    let ens_some = forall(
        "t",
        implies(
            eq(var("self"), logic_fn_call("Some", vec![var("t")])),
            eq(var("result"), logic_fn_call("Some", vec![var("t")])),
        ),
    );
    // ensures: self == None ==> result == None
    let ens_none = implies(
        eq(var("self"), logic_fn_call("None", vec![])),
        eq(var("result"), logic_fn_call("None", vec![])),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_some, ens_none]).return_expr(Some(&body)),
    );

    assert!(
        result.is_ok(),
        "Option as_ref identity pipeline should encode (#1296): {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "Option as_ref identity with quantified postcondition should verify: \
         result == self satisfies all constructor-preserving postconditions (#1296): {vr:?}"
    );
}
