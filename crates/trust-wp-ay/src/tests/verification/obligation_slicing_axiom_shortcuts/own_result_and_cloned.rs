// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
/// Full verification pipeline test for `OwnResult::and` pattern.
///
/// Models the compat shape:
/// ```rust
/// #[ensures(forall<t: T> self == OwnResult::Ok(t) ==> result == res)]
/// #[ensures(forall<e: E> self == OwnResult::Err(e) ==> result == OwnResult::Err(e))]
/// fn and<U>(self, res: OwnResult<U, E>) -> OwnResult<U, E> {
///     match self { OwnResult::Ok(x) => res, OwnResult::Err(e) => OwnResult::Err(e) }
/// }
/// ```
///
/// Guards against SortFallbackToIntFromLogicFn demotion for qualified
/// `OwnResult::Ok`/`OwnResult::Err` constructor calls when the ADT is
/// pre-declared via adt_decls. (#1296)
#[test]
#[timeout(30000)]
fn test_own_result_and_pipeline_no_demotion() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let own_result_sort = ExprSort::Datatype(intern_sort_name("OwnResult"));

    // Body: match self { OwnResult::Ok(x) => res, OwnResult::Err(e) => OwnResult::Err(e) }
    // `res` is annotated with OwnResult sort (driver provides this from MIR types).
    let body = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "OwnResult::Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                },
                var_with_sort("res", own_result_sort.clone()),
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

    // ensures: forall<t: T> self == OwnResult::Ok(t) ==> result == res
    let ens_ok = forall_with_sort(
        "t",
        t_sort.clone(),
        implies(
            eq(var("self"), logic_fn_call("OwnResult::Ok", vec![var("t")])),
            eq(var("result"), var_with_sort("res", own_result_sort.clone())),
        ),
    );
    // ensures: forall<e: E> self == OwnResult::Err(e) ==> result == OwnResult::Err(e)
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
        "OwnResult::and should encode without errors (#1296): {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "OwnResult::and should verify without demotion — forall constructor matching with pre-declared ADT (#1296): {vr:?}"
    );
}
