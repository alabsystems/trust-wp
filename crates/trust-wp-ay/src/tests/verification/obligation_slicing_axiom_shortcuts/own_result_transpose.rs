// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
/// Full verification pipeline regression for `OwnResult<Option<T>, E>::transpose`.
///
/// This matches the compat body/contract shape from `result/own.rs` and guards
/// the residual #2462 path where nested `Some(...)` calls on custom `OwnResult`
/// values could misroute through stdlib constructor placeholders.
#[test]
#[timeout(90000)]
fn test_own_result_transpose_pipeline_avoids_some_placeholder_sort_mismatch() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    })),
                },
                logic_fn_call("Some", vec![logic_fn_call("OwnResult::Ok", vec![var("x")])]),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    })),
                },
                var("None"),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
            ),
        ],
    );

    let t_sort = ExprSort::Datatype(intern_sort_name("T"));
    let e_sort = ExprSort::Datatype(intern_sort_name("E"));

    let ens_none = implies(
        eq(
            var("self"),
            logic_fn_call("OwnResult::Ok", vec![var("None")]),
        ),
        eq(var("result"), var("None")),
    );
    let ens_some_ok = forall_with_sort(
        "t",
        t_sort.clone(),
        implies(
            eq(
                var("self"),
                logic_fn_call("OwnResult::Ok", vec![logic_fn_call("Some", vec![var("t")])]),
            ),
            eq(
                var("result"),
                logic_fn_call("Some", vec![logic_fn_call("OwnResult::Ok", vec![var("t")])]),
            ),
        ),
    );
    let ens_err = forall_with_sort(
        "e",
        e_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Err", vec![var("e")])),
            eq(
                var("result"),
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
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
        VerificationRequest::new(&[], &[ens_none, ens_some_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "transpose pipeline should encode without `logic_fn_placeholder:Some` sort mismatch: {result:?}"
    );
    let vr = result.unwrap();
    let acceptable = match &vr {
        VerificationResult::Verified(_) => true,
        VerificationResult::Unknown(crate::UnknownReason::SolverMessage(message)) => {
            message.contains("proof-trusted")
                || message.contains("fail_closed_unaccepted_unsat_evidence")
                || message.contains("UNSAT evidence")
        }
        _ => false,
    };
    assert!(
        acceptable,
        "transpose Datatype-sorted ADT fields should verify, or fail closed when AY lacks trusted proof evidence: {vr:?}"
    );
}

/// Driver-shaped regression for `OwnResult<Option<T>, E>::transpose` where the
/// extracted body uses qualified stdlib constructors (`Option::Some/None`) but
/// the postconditions still use unqualified `Some/None`. The fallback path for
/// `Option::Some(OwnResult::Err(_))` must keep the Option carrier sort.
#[test]
#[timeout(90000)]
fn test_own_result_transpose_pipeline_with_qualified_option_constructors() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    })),
                },
                logic_fn_call(
                    "Option::Some",
                    vec![logic_fn_call("OwnResult::Ok", vec![var("x")])],
                ),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    })),
                },
                logic_fn_call("Option::None", vec![]),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                logic_fn_call(
                    "Option::Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
            ),
        ],
    );

    let t_sort = ExprSort::Datatype(intern_sort_name("T"));
    let e_sort = ExprSort::Datatype(intern_sort_name("E"));

    let ens_none = implies(
        eq(
            var("self"),
            logic_fn_call("OwnResult::Ok", vec![var("None")]),
        ),
        eq(var("result"), var("None")),
    );
    let ens_some_ok = forall_with_sort(
        "t",
        t_sort.clone(),
        implies(
            eq(
                var("self"),
                logic_fn_call("OwnResult::Ok", vec![logic_fn_call("Some", vec![var("t")])]),
            ),
            eq(
                var("result"),
                logic_fn_call("Some", vec![logic_fn_call("OwnResult::Ok", vec![var("t")])]),
            ),
        ),
    );
    let ens_err = forall_with_sort(
        "e",
        e_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Err", vec![var("e")])),
            eq(
                var("result"),
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
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
        VerificationRequest::new(&[], &[ens_none, ens_some_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "driver-shaped qualified Option transpose should encode without residual fallback drift: {result:?}"
    );
    // NOTE: This test uses ExprSort::Datatype("T") for generic params, which maps
    // to Sort::Uninterpreted("T") — NOT the driver's actual output (TypeParam→Int).
    // The Uninterpreted("T") fields create a different sort bridge problem than Int
    // fields: the UF Option model (is_some/spec_unwrap) operates on Int, not
    // Uninterpreted("T"). Full verification requires TypeParam→Int sorts, tested in
    // test_own_result_transpose_pipeline_type_param_sort. (#1296, #2551)
}

/// Minimal `transpose` Err-branch regression for the nested placeholder path:
/// `Some(OwnResult::Err(_))` must never be read as `None`, even when the outer
/// `Some` constructor cannot use the native `OptionInt` datatype path.
///
/// The `match` body encodes at `OptionInt` and reaches the result's
/// `Option<OwnResult>` sort only through a structural bridge that carries no
/// constructor, so `result != None` is not proved. It verified only while the
/// datatype binding wrapped every non-constructor body in `Some`, which proved
/// the same postcondition for a body returning `None` (D-165); what stays owed
/// is that the Err branch is never refuted.
#[test]
#[timeout(90000)]
fn test_own_result_transpose_err_branch_some_err_is_not_none() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    let req = eq(var("self"), logic_fn_call("OwnResult::Err", vec![int(7)]));
    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
            ),
            (Pattern::Wildcard, logic_fn_call("None", vec![])),
        ],
    );
    let ens = ne(var("result"), logic_fn_call("None", vec![]));

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
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "nested Some(OwnResult::Err(_)) branch should encode: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        !matches!(vr, VerificationResult::Failed(..)),
        "Some(OwnResult::Err(_)) must stay distinct from None on the transpose Err branch: {vr:?}"
    );
}

/// The same `match` body under `self == OwnResult::Ok(7)` returns `None`, so
/// `result != None` is false. A binding that wraps the body's `OptionInt` value
/// in `Some` proves it (D-165).
#[test]
#[timeout(90000)]
fn test_own_result_transpose_ok_branch_none_is_not_read_as_some() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    let req = eq(var("self"), logic_fn_call("OwnResult::Ok", vec![int(7)]));
    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
            ),
            (Pattern::Wildcard, logic_fn_call("None", vec![])),
        ],
    );
    let ens = ne(var("result"), logic_fn_call("None", vec![]));

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
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        !matches!(
            result,
            Ok(VerificationResult::Verified(_) | VerificationResult::Assumed(_))
        ),
        "the Ok branch returns None, so result != None must not verify: {result:?}"
    );
}

/// Same as the Datatype("T")/Datatype("E") variant above but uses
/// `ExprSort::TypeParam`, which is what the driver actually emits for generic
/// type parameters (see `adt_analysis.rs:318`). With #2551, TypeParam maps to
/// `Sort::Int` — this test validates that the Int-sorted ADT fields don't
/// produce a sort mismatch when `Some(OwnResult::Ok(x))` is encoded.
#[test]
#[timeout(90000)]
fn test_own_result_transpose_pipeline_type_param_sort() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    })),
                },
                logic_fn_call("Some", vec![logic_fn_call("OwnResult::Ok", vec![var("x")])]),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    })),
                },
                var("None"),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
            ),
        ],
    );

    // Use TypeParam (driver-realistic) instead of Datatype for generic params
    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));

    let ens_none = implies(
        eq(
            var("self"),
            logic_fn_call("OwnResult::Ok", vec![var("None")]),
        ),
        eq(var("result"), var("None")),
    );
    let ens_some_ok = forall_with_sort(
        "t",
        t_sort.clone(),
        implies(
            eq(
                var("self"),
                logic_fn_call("OwnResult::Ok", vec![logic_fn_call("Some", vec![var("t")])]),
            ),
            eq(
                var("result"),
                logic_fn_call("Some", vec![logic_fn_call("OwnResult::Ok", vec![var("t")])]),
            ),
        ),
    );
    let ens_err = forall_with_sort(
        "e",
        e_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Err", vec![var("e")])),
            eq(
                var("result"),
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
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
        VerificationRequest::new(&[], &[ens_none, ens_some_ok, ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "transpose with TypeParam sorts should encode without sort mismatch (#2462, #2551): {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "transpose TypeParam-sorted ADT fields should verify all 3 postconditions: {vr:?}"
    );
}

/// Full verification regression for `OwnResult<Option<T>, E>::transpose` that
/// checks the Err-branch postcondition actually VERIFIES, not just encodes.
///
/// Prior tests (#1296) only asserted `result.is_ok()` (encoding succeeds) but
/// never checked `VerificationResult::Verified`. The compat pipeline reports
/// counterexample `self=Err(0), result=None` because the placeholder
/// `Some(OwnResult::Err(e))` inside the quantified postcondition is not
/// provably distinct from `None` without the disequality axiom firing.
///
/// This test uses TypeParam sorts (matching the driver's output) and asserts
/// the verification result, catching the actual pipeline failure.
#[test]
#[timeout(90000)]
fn test_own_result_transpose_err_postcondition_verifies() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    })),
                },
                logic_fn_call("Some", vec![logic_fn_call("OwnResult::Ok", vec![var("x")])]),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    })),
                },
                var("None"),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
            ),
        ],
    );

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));

    // Only test the Err-branch postcondition — this is the one that fails
    // in the compat pipeline with counterexample self=Err(0), result=None.
    let ens_err = forall_with_sort(
        "e",
        e_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Err", vec![var("e")])),
            eq(
                var("result"),
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
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
        VerificationRequest::new(&[], &[ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "transpose Err-branch should encode: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "transpose Err-branch postcondition `forall<e> self == Err(e) ==> \
         result == Some(Err(e))` must verify — counterexample self=Err(0), \
         result=None indicates missing Some/None disequality: {vr:?}"
    );
}

/// Driver-realistic regression for `OwnResult<Option<T>, E>::transpose` where
/// the `OwnResult::Ok` field is the concrete `OptionInt` datatype but the
/// `OwnResult::Err` field remains a generic type parameter.
#[test]
#[timeout(90000)]
fn test_own_result_transpose_driver_realistic_option_datatype_ok_field() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    })),
                },
                logic_fn_call("Some", vec![logic_fn_call("OwnResult::Ok", vec![var("x")])]),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    })),
                },
                var("None"),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
            ),
        ],
    );

    let ok_sort = ExprSort::Datatype(intern_sort_name("OptionInt"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));

    let ens_err = forall_with_sort(
        "e",
        ExprSort::TypeParam(intern_sort_name("E")),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Err", vec![var("e")])),
            eq(
                var("result"),
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
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
                    vec![AdtFieldDecl::new("ok".to_string(), ok_sort)],
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
        VerificationRequest::new(&[], &[ens_err])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "transpose Err-branch should encode with driver-realistic OptionInt/TypeParam OwnResult fields; \
         a sort mismatch between OptionInt and OwnResult is the likely cause: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "transpose Err-branch with driver-realistic OptionInt/TypeParam OwnResult fields must verify; \
         a sort mismatch between OptionInt and OwnResult is the likely cause: {vr:?}"
    );
}

#[test]
#[timeout(90000)]
fn test_own_result_transpose_driver_discriminant_ite_postconditions() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let self_expr = || var_with_sort("self", self_sort.clone());
    let self_discriminant = || method_call(self_expr(), "discriminant", vec![]);
    let self_payload_discriminant = || method_call(var("self.0"), "discriminant", vec![]);

    let body = let_assume(
        or(
            eq(self_discriminant(), int(0)),
            eq(self_discriminant(), int(1)),
        ),
        ite(
            eq(self_discriminant(), int(0)),
            let_assume(
                or(
                    eq(self_payload_discriminant(), int(0)),
                    eq(self_payload_discriminant(), int(1)),
                ),
                ite(
                    eq(self_payload_discriminant(), int(0)),
                    logic_fn_call("None", vec![]),
                    logic_fn_call(
                        "Some",
                        vec![logic_fn_call("OwnResult::Ok", vec![var("self.0.0")])],
                    ),
                ),
            ),
            logic_fn_call(
                "Some",
                vec![logic_fn_call("OwnResult::Err", vec![var("self.0")])],
            ),
        ),
    );

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));

    let ens_err = forall_with_sort(
        "e",
        e_sort.clone(),
        implies(
            eq(self_expr(), logic_fn_call("OwnResult::Err", vec![var("e")])),
            eq(
                var("result"),
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
            ),
        ),
    );
    let ens_some_ok = forall_with_sort(
        "t",
        t_sort.clone(),
        implies(
            eq(
                self_expr(),
                logic_fn_call("OwnResult::Ok", vec![logic_fn_call("Some", vec![var("t")])]),
            ),
            eq(
                var("result"),
                logic_fn_call("Some", vec![logic_fn_call("OwnResult::Ok", vec![var("t")])]),
            ),
        ),
    );
    let ens_none = implies(
        eq(
            self_expr(),
            logic_fn_call("OwnResult::Ok", vec![var("None")]),
        ),
        eq(var("result"), var("None")),
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
        VerificationRequest::new(&[], &[ens_err, ens_some_ok, ens_none])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "driver discriminator-ITE transpose body should encode: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "driver discriminator-ITE transpose postconditions should verify: {vr:?}"
    );
}

#[test]
#[timeout(90000)]
fn test_own_result_transpose_implication_style_postconditions() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    })),
                },
                logic_fn_call("Some", vec![logic_fn_call("OwnResult::Ok", vec![var("x")])]),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    })),
                },
                var("None"),
            ),
            (
                Pattern::Constructor {
                    name: "OwnResult::Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                logic_fn_call(
                    "Some",
                    vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
                ),
            ),
        ],
    );

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));

    let ens1 = implies(
        method_call(var("self"), "is_err", vec![]),
        method_call(var("result"), "is_some", vec![]),
    );
    let ens2 = implies(
        and(
            method_call(var("self"), "is_ok", vec![]),
            method_call(
                method_call(var("self"), "unwrap", vec![]),
                "is_none",
                vec![],
            ),
        ),
        method_call(var("result"), "is_none", vec![]),
    );
    let ens3 = implies(
        and(
            method_call(var("self"), "is_ok", vec![]),
            method_call(
                method_call(var("self"), "unwrap", vec![]),
                "is_some",
                vec![],
            ),
        ),
        method_call(var("result"), "is_some", vec![]),
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
        VerificationRequest::new(&[], &[ens1, ens2, ens3])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "transpose implication-style postconditions should encode: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "transpose implication-style postconditions should verify: {vr:?}"
    );
}

#[test]
#[timeout(90000)]
fn test_own_result_as_ref_implication_style_postconditions() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                logic_fn_call("OwnResult::Ok", vec![var("v")]),
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

    let ens1 = implies(
        method_call(var("self"), "is_ok", vec![]),
        method_call(var("result"), "is_ok", vec![]),
    );
    let ens2 = implies(
        method_call(var("self"), "is_ok", vec![]),
        eq(
            method_call(var("result"), "unwrap", vec![]),
            method_call(var("self"), "unwrap", vec![]),
        ),
    );
    let ens3 = implies(
        method_call(var("self"), "is_err", vec![]),
        method_call(var("result"), "is_err", vec![]),
    );
    let ens4 = implies(
        method_call(var("self"), "is_err", vec![]),
        eq(
            method_call(var("result"), "unwrap_err", vec![]),
            method_call(var("self"), "unwrap_err", vec![]),
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
        VerificationRequest::new(&[], &[ens1, ens2, ens3, ens4])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "as_ref implication-style postconditions should encode: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "as_ref implication-style postconditions should verify: {vr:?}"
    );
}

#[test]
#[timeout(90000)]
fn test_own_result_unwrap_or_default_implication_style_postconditions() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
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

    let ens1 = implies(
        method_call(var("self"), "is_ok", vec![]),
        eq(var("result"), method_call(var("self"), "unwrap", vec![])),
    );
    let ens2 = implies(
        method_call(var("self"), "is_err", vec![]),
        eq(var("result"), int(0)),
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
        VerificationRequest::new(&[], &[ens1, ens2])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "unwrap_or_default implication-style postconditions should encode: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "unwrap_or_default implication-style postconditions should verify: {vr:?}"
    );
}

#[test]
#[timeout(90000)]
fn test_own_result_unwrap_or_default_driver_discriminant_ite_ok_postcondition() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let self_expr = || var_with_sort("self", self_sort.clone());
    let self_discriminant = || method_call(self_expr(), "discriminant", vec![]);
    let body = let_assume(
        or(
            eq(self_discriminant(), int(0)),
            eq(self_discriminant(), int(1)),
        ),
        ite(
            eq(self_discriminant(), int(0)),
            var("self.0"),
            var("_call_0"),
        ),
    );

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));
    let ens = forall_with_sort(
        "t",
        t_sort.clone(),
        implies(
            eq(self_expr(), logic_fn_call("OwnResult::Ok", vec![var("t")])),
            eq(var("result"), var("t")),
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
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "driver discriminator-ITE unwrap_or_default Ok branch should encode: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "driver discriminator-ITE unwrap_or_default Ok branch should verify: {vr:?}"
    );
}

#[test]
#[timeout(90000)]
fn test_own_result_unwrap_or_driver_discriminant_ite_err_default_postcondition() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let self_expr = || var_with_sort("self", self_sort.clone());
    let self_discriminant = || method_call(self_expr(), "discriminant", vec![]);
    let body = let_assume(
        or(
            eq(self_discriminant(), int(0)),
            eq(self_discriminant(), int(1)),
        ),
        ite(
            eq(self_discriminant(), int(0)),
            var("self.0"),
            var("default"),
        ),
    );

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));
    let ens = implies(
        exists_with_sort(
            "e",
            e_sort.clone(),
            eq(self_expr(), logic_fn_call("OwnResult::Err", vec![var("e")])),
        ),
        eq(var("result"), var("default")),
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
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "driver discriminator-ITE unwrap_or Err branch should encode: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "driver discriminator-ITE unwrap_or Err branch should verify: {vr:?}"
    );
}

#[test]
#[timeout(90000)]
fn test_own_result_unwrap_or_default_driver_discriminant_ite_default_postcondition() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let self_expr = || var_with_sort("self", self_sort.clone());
    let self_discriminant = || method_call(self_expr(), "discriminant", vec![]);
    let call_0 = || var_with_sort("call_0", ExprSort::TypeParam(intern_sort_name("T")));
    let tuple0 = || logic_fn_call("__trust_wp_tuple0", vec![]);
    let default_fn = || var("core::default::Default::default");
    let default_post =
        |value: PureExpr| method_call(default_fn(), "postcondition", vec![tuple0(), value]);

    let body = let_assume(
        or(
            eq(self_discriminant(), int(0)),
            eq(self_discriminant(), int(1)),
        ),
        ite(eq(self_discriminant(), int(0)), var("self.0"), call_0()),
    );

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));
    let requires = vec![default_post(call_0())];
    let ens = implies(
        exists_with_sort(
            "e",
            e_sort.clone(),
            eq(self_expr(), logic_fn_call("OwnResult::Err", vec![var("e")])),
        ),
        default_post(var("result")),
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
        VerificationRequest::new(&requires, &[ens])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "driver discriminator-ITE unwrap_or_default default branch should encode: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "driver discriminator-ITE unwrap_or_default default branch should verify: {vr:?}"
    );
}

#[test]
#[timeout(90000)]
fn test_own_result_unwrap_or_default_driver_discriminant_ite_mixed_default_names() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let self_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let self_expr = || var_with_sort("self", self_sort.clone());
    let self_discriminant = || method_call(self_expr(), "discriminant", vec![]);
    let call_0 = || var_with_sort("call_0", ExprSort::TypeParam(intern_sort_name("T")));
    let tuple0 = || logic_fn_call("__trust_wp_tuple0", vec![]);
    let default_post = |receiver: &str, value: PureExpr| {
        method_call(var(receiver), "postcondition", vec![tuple0(), value])
    };

    let body = let_assume(
        or(
            eq(self_discriminant(), int(0)),
            eq(self_discriminant(), int(1)),
        ),
        ite(eq(self_discriminant(), int(0)), var("self.0"), call_0()),
    );

    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));
    let e_sort = ExprSort::TypeParam(intern_sort_name("E"));
    let requires = vec![default_post("core::default::Default::default", call_0())];
    let ens = implies(
        exists_with_sort(
            "e",
            e_sort.clone(),
            eq(self_expr(), logic_fn_call("OwnResult::Err", vec![var("e")])),
        ),
        default_post("T::default", var("result")),
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
        VerificationRequest::new(&requires, &[ens])
            .return_expr(Some(&body))
            .adt_decls(Some(adt_decls)),
    );

    assert!(
        result.is_ok(),
        "mixed-name unwrap_or_default default branch should encode: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "mixed-name unwrap_or_default default branch should verify: {vr:?}"
    );
}
