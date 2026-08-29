// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

use super::*;

fn own_result_adt_decls(t_sort: ExprSort, e_sort: ExprSort) -> HashMap<String, AdtDecl> {
    HashMap::from([(
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
    )])
}

fn cloned_ensures(self_expr: PureExpr, own_result_sort: ExprSort) -> PureExpr {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    let pair = logic_fn_call(
        &tuple_logic_fn_name(2),
        vec![self_expr, var_with_sort("result", own_result_sort)],
    );
    match_expr(
        pair,
        vec![
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "OwnResult::Ok".to_string(),
                        inner: Some(Box::new(Pattern::Binding("s".to_string()))),
                    },
                    Pattern::Constructor {
                        name: "OwnResult::Ok".to_string(),
                        inner: Some(Box::new(Pattern::Binding("r".to_string()))),
                    },
                ]),
                logic_fn_call("T::clone.postcondition", vec![var("s"), var("r")]),
            ),
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "OwnResult::Err".to_string(),
                        inner: Some(Box::new(Pattern::Binding("s".to_string()))),
                    },
                    Pattern::Constructor {
                        name: "OwnResult::Err".to_string(),
                        inner: Some(Box::new(Pattern::Binding("r".to_string()))),
                    },
                ]),
                eq(var("s"), var("r")),
            ),
            (Pattern::Wildcard, bool_expr(false)),
        ],
    )
}

/// Match the real extracted `OwnResult<&T, E>::cloned` shape more closely:
/// the clone postcondition is recorded against the projected receiver payload
/// (`self.0`) and the body reconstructs `OwnResult::Ok(call_result)` inside a
/// `match self { ... }`.
///
/// This is the decisive successor to the former explicit-bridge reduction:
/// it uses the real projected receiver shape and requires `Verified` rather
/// than accepting `Unknown` or a caught solver panic.
///
/// If this verifies, the remaining compat failure is not in the core
/// `(self.0, call_N, match self { Ok => Ok(call_N) })` proof shape and likely
/// lives higher in the driver/contract pipeline. If it fails, the ay side is
/// still missing a bridge for the extracted shape. (#1296)
#[test]
#[timeout(90000)]
fn test_own_result_cloned_ok_ok_extracted_projection_shape_verifies() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));
    let own_result_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let self_expr = var_with_sort("self", own_result_sort.clone());
    let clone_result = var_with_sort("call_5", t_sort.clone());

    let req = logic_fn_call(
        "T::clone.postcondition",
        vec![var("self.0"), clone_result.clone()],
    );

    let body = match_expr(
        self_expr.clone(),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("t".to_string()))),
                },
                logic_fn_call("OwnResult::Ok", vec![clone_result]),
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

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[cloned_ensures(self_expr, own_result_sort)])
            .return_expr(Some(&body))
            .adt_decls(Some(own_result_adt_decls(t_sort, e_sort))),
    );

    assert!(
        result.is_ok(),
        "extracted cloned projection shape should encode without errors: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "extracted cloned projection shape should verify: {vr:?}"
    );
}

/// The `copied` postcondition for `OwnResult<&T, E>` is structurally simpler
/// than `cloned`: no `T::clone.postcondition` involved, just dereference
/// identity. In the RustHorn encoding, `&T` is transparent so `*t == t`.
///
/// Postcondition:
///   forall<t> self == OwnResult::Ok(t) ==> result == OwnResult::Ok(t)
///   forall<e> self == OwnResult::Err(e) ==> result == OwnResult::Err(e)
///
/// Body:
///   match self { Ok(t) => Ok(t), Err(e) => Err(e) }
///
/// This should verify trivially because the body is identity through the match.
#[test]
#[timeout(30000)]
fn test_own_result_copied_ok_identity_postcondition_verifies() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));
    let own_result_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let self_expr = var_with_sort("self", own_result_sort.clone());

    // The body: match self { Ok(t) => Ok(t), Err(e) => Err(e) }
    // Since &T is transparent in RustHorn, `*t == t`, so the body is identity.
    let body = match_expr(
        self_expr.clone(),
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

    // Postcondition 1: forall<t> self == Ok(t) ==> result == Ok(t)
    let ens_ok = PureExpr::Forall {
        var: "t".to_string(),
        var_sort: Some(t_sort.clone()),
        body: Arc::new(implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
            eq(
                var_with_sort("result", own_result_sort.clone()),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
        )),
        triggers: vec![],
    };

    // Postcondition 2: forall<e> self == Err(e) ==> result == Err(e)
    let ens_err = PureExpr::Forall {
        var: "e".to_string(),
        var_sort: Some(e_sort.clone()),
        body: Arc::new(implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
            eq(
                var_with_sort("result", own_result_sort.clone()),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
        )),
        triggers: vec![],
    };

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(own_result_adt_decls(t_sort, e_sort))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "copied identity postcondition must verify: {result:?}"
    );
}

/// The real `copied` contract from `result/own.rs` uses `*t` (deref) in the
/// postcondition: `forall<t: &T> self == OwnResult::Ok(t) ==> result == OwnResult::Ok(*t)`.
///
/// The contract parser produces `Deref(Var("t"))` for `*t`. The encoder must
/// collapse `Deref(Var("t"))` to `Var("t")` when `t` is quantifier-bound,
/// because quantifier-bound variables in RustHorn are pure values without
/// temporal state (see wrapper.rs Phase 1, #717).
///
/// This test adds the explicit `Deref` to the postcondition to verify the
/// collapse works end-to-end with ADT matching.
#[test]
#[timeout(30000)]
fn test_own_result_copied_deref_in_postcondition_verifies() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));
    let own_result_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let self_expr = var_with_sort("self", own_result_sort.clone());

    // Body: match self { Ok(t) => Ok(t), Err(e) => Err(e) }
    let body = match_expr(
        self_expr.clone(),
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

    // Postcondition with explicit Deref(*t):
    // forall<t> self == Ok(t) ==> result == Ok(Deref(t))
    let ens_ok = PureExpr::Forall {
        var: "t".to_string(),
        var_sort: Some(t_sort.clone()),
        body: Arc::new(implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Ok", vec![var("t")]),
            ),
            eq(
                var_with_sort("result", own_result_sort.clone()),
                logic_fn_call("OwnResult::Ok", vec![deref(var("t"))]),
            ),
        )),
        triggers: vec![],
    };

    let ens_err = PureExpr::Forall {
        var: "e".to_string(),
        var_sort: Some(e_sort.clone()),
        body: Arc::new(implies(
            eq(
                self_expr.clone(),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
            eq(
                var_with_sort("result", own_result_sort.clone()),
                logic_fn_call("OwnResult::Err", vec![var("e")]),
            ),
        )),
        triggers: vec![],
    };

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(own_result_adt_decls(t_sort, e_sort))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "copied Deref(*t) postcondition must verify: {result:?}"
    );
}
