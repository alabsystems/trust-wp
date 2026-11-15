// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// The former axiom-only shortcut returned `Assumed` with no solver query.
/// These shapes are now ordinary obligations whose claim is unprovable from
/// the uninterpreted symbols involved: they must be refused (Failed or
/// Unknown), never Verified and never the unqueried Assumed.
fn is_real_unproved_obligation(result: &VerificationResult) -> bool {
    matches!(
        result,
        VerificationResult::Failed(_) | VerificationResult::Unknown(_)
    )
}

/// A true universal lemma with a trivial body is proved, not assumed.
#[test]
#[timeout(30000)]
fn test_former_axiom_only_true_universal_lemma_verifies() {
    let ens = forall("i", eq(var("i"), var("i")));
    let unit_body = logic_fn_call("__trust_wp_tuple0", vec![]);
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).return_expr(Some(&unit_body)),
    )
    .expect("true universal lemma encoding should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "forall i. i == i with a trivial body must verify with a real proof: {result:?}"
    );
}

/// A false universal lemma with a trivial body is refuted, not assumed.
#[test]
#[timeout(30000)]
fn test_former_axiom_only_false_universal_lemma_fails() {
    let ens = forall("i", eq(var("i"), int(5)));
    let unit_body = logic_fn_call("__trust_wp_tuple0", vec![]);
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).return_expr(Some(&unit_body)),
    )
    .expect("false universal lemma encoding should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "forall i. i == 5 with a trivial body must be refuted: {result:?}"
    );
}
// ── Axiom-only postcondition tests (#1753) ─────────────────────────

/// Former axiom-only shape: unit body, no requires, forall postcondition.
///
/// This is the cc/fset.rs pattern. It used to short-circuit to `Assumed`
/// without a solver query (#1753); it now carries a real obligation. Over an
/// uninterpreted `interval`/`contains` the claim is not provable, so it must
/// be neither `Verified` nor the old unqueried `Assumed`.
#[test]
#[timeout(30000)]
fn test_axiom_only_forall_unit_body_verified() {
    let ens = forall(
        "i",
        forall(
            "j",
            forall(
                "k",
                eq(
                    method_call(
                        method_call(var("i"), "interval", vec![var("j")]),
                        "contains",
                        vec![var("k")],
                    ),
                    and(le(var("i"), var("k")), lt(var("k"), var("j"))),
                ),
            ),
        ),
    );

    let unit_body = logic_fn_call("__trust_wp_tuple0", vec![]);
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).return_expr(Some(&unit_body)),
    )
    .expect("axiom-only encoding should not error");
    assert!(
        is_real_unproved_obligation(&result),
        "former axiom-only shape must reach the solver and not verify: axiom-only function with forall ensures + unit body : {result:?}"
    );
}

/// Former axiom-only shape: None body, forall postcondition over an
/// uninterpreted method. Not provable, so not Verified and never Assumed.
#[test]
#[timeout(30000)]
fn test_axiom_only_forall_none_body_verified() {
    let ens = forall("x", gt(method_call(var("x"), "f", vec![]), int(0)));

    let result = verify_function_with_modes(VerificationRequest::new(&[], &[ens]))
        .expect("axiom-only encoding should not error");
    assert!(
        is_real_unproved_obligation(&result),
        "former axiom-only shape must reach the solver and not verify: axiom-only function with forall ensures + None body : {result:?}"
    );
}

/// Non-axiom: has requires -> normal verification, not the axiom shortcut.
#[test]
#[timeout(30000)]
fn test_non_axiom_has_requires_not_shortcutted() {
    let req = gt(var("x"), int(0));
    let ens = forall("y", gt(var("y"), int(0)));

    let result = verify_function_with_modes(VerificationRequest::new(&[req], &[ens]))
        .expect("encoding should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "function with requires should fail normal verification rather than use the axiom-only shortcut: {result:?}"
    );
}

/// Non-axiom: has non-trivial body -> normal verification.
#[test]
#[timeout(30000)]
fn test_non_axiom_nontrivial_body_not_shortcutted() {
    let ens = forall("y", gt(var("y"), int(0)));
    let body = add(var("x"), int(1));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("encoding should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "function with non-trivial body should fail normal verification rather than use the axiom-only shortcut: {result:?}"
    );
}

/// Non-axiom: non-quantified ensures -> normal verification.
#[test]
#[timeout(30000)]
fn test_non_axiom_non_quantified_ensures_not_shortcutted() {
    let ens = gt(var("result"), int(0));
    let unit_body = logic_fn_call("__trust_wp_tuple0", vec![]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).return_expr(Some(&unit_body)),
    )
    .expect("encoding should not error");
    assert!(
        matches!(
            result,
            VerificationResult::Unknown(UnknownReason::Demoted(ref reason))
                if reason.contains("sort-coercion bridge in negated goal")
        ),
        "non-quantified ensures should take normal verification and fail closed on its unit/Int sort bridge rather than use the axiom-only shortcut: {result:?}"
    );
}

/// Non-axiom: quantified ensures that mention `result` use normal verification.
#[test]
#[timeout(30000)]
fn test_non_axiom_forall_mentions_result_not_shortcutted() {
    let ens = forall("x", gt(var("result"), var("x")));

    let result = verify_function_with_modes(VerificationRequest::new(&[], &[ens]))
        .expect("encoding should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "forall postcondition mentioning result should fail normal verification rather than use the axiom-only shortcut: {result:?}"
    );
}

/// Former axiom-only shape with multiple forall ensures: each is a real
/// obligation. `x.abs() >= 0` over an uninterpreted `abs` is not provable.
#[test]
#[timeout(30000)]
fn test_axiom_only_multiple_forall_ensures_verified() {
    let ens1 = forall("x", eq(method_call(var("x"), "id", vec![]), var("x")));
    let ens2 = forall("x", ge(method_call(var("x"), "abs", vec![]), int(0)));

    let result = verify_function_with_modes(VerificationRequest::new(&[], &[ens1, ens2]))
        .expect("axiom-only encoding should not error");
    assert!(
        is_real_unproved_obligation(&result),
        "former axiom-only shape must reach the solver and not verify: multiple forall ensures with no body : {result:?}"
    );
}

/// Non-axiom: type invariants present -> normal verification (could be a lemma).
#[test]
#[timeout(30000)]
fn test_non_axiom_type_invariants_not_shortcutted() {
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Pos".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let ens = forall("x", gt(var("x"), int(0)));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).type_invariants(Some(&[inv_def])),
    )
    .expect("encoding should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "function with type invariants should fail normal verification rather than use the axiom-only shortcut: {result:?}"
    );
}

/// Non-axiom: non-empty ghost context must disable axiom-only shortcut.
#[test]
#[timeout(30000)]
fn test_non_axiom_ghost_context_not_shortcutted() {
    let ens = forall("x", gt(method_call(var("x"), "f", vec![]), int(0)));
    let ghost_facts = vec![eq(var("g"), bool_expr(true))];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).ghost_context(Some(&ghost_facts)),
    )
    .expect("encoding should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "non-empty ghost context should fail normal verification rather than use the axiom-only shortcut: {result:?}"
    );
}

/// cc/fset.rs `map_spec` pattern: forall with nested exists in body.
///
/// ```text
/// #[ensures(forall<xs: FSet<T>, f: Mapping<T, U>, y: U>
///   xs.map(f).contains(y) == exists<x: T> xs.contains(x) && f.get(x) == y)]
/// pub fn map_spec<T, U>() {}
/// ```
///
/// The outermost expression is Forall, so `is_universal_quantifier` returns
/// true even though the body contains an existential. (#1753)
#[test]
#[timeout(30000)]
fn test_axiom_only_fset_map_spec_pattern() {
    // forall<xs, f, y> xs.map(f).contains(y) == (exists<x> xs.contains(x) && f.get(x) == y)
    let inner_exists = exists(
        "x",
        and(
            method_call(var("xs"), "contains", vec![var("x")]),
            eq(method_call(var("f"), "get", vec![var("x")]), var("y")),
        ),
    );
    let ens = forall(
        "xs",
        forall(
            "f",
            forall(
                "y",
                eq(
                    method_call(
                        method_call(var("xs"), "map", vec![var("f")]),
                        "contains",
                        vec![var("y")],
                    ),
                    inner_exists,
                ),
            ),
        ),
    );

    let unit_body = logic_fn_call("__trust_wp_tuple0", vec![]);
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).return_expr(Some(&unit_body)),
    )
    .expect("map_spec axiom-only encoding should not error");
    assert!(
        is_real_unproved_obligation(&result),
        "former axiom-only shape must reach the solver and not verify: cc/fset.rs map_spec pattern (forall with nested exists) : {result:?}"
    );
}

/// cc/fset.rs `filter_spec` pattern: forall with conjunction body.
///
/// ```text
/// #[ensures(forall<xs: FSet<T>, f: Mapping<T, bool>, x: T>
///   xs.filter(f).contains(x) == (xs.contains(x) && f.get(x)))]
/// pub fn filter_spec<T>() {}
/// ```
#[test]
#[timeout(30000)]
fn test_axiom_only_fset_filter_spec_pattern() {
    // forall<xs, f, x> xs.filter(f).contains(x) == (xs.contains(x) && f.get(x))
    let ens = forall(
        "xs",
        forall(
            "f",
            forall(
                "x",
                eq(
                    method_call(
                        method_call(var("xs"), "filter", vec![var("f")]),
                        "contains",
                        vec![var("x")],
                    ),
                    and(
                        method_call(var("xs"), "contains", vec![var("x")]),
                        method_call(var("f"), "get", vec![var("x")]),
                    ),
                ),
            ),
        ),
    );

    let unit_body = logic_fn_call("__trust_wp_tuple0", vec![]);
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).return_expr(Some(&unit_body)),
    )
    .expect("filter_spec axiom-only encoding should not error");
    assert!(
        is_real_unproved_obligation(&result),
        "former axiom-only shape must reach the solver and not verify: cc/fset.rs filter_spec pattern : {result:?}"
    );
}

/// call_in_contract.rs regression: Self::f() == () with logic function f available.
///
/// Trait `Foo` has `#[logic] fn f() {}` (body = unit, registered as `logic_f`).
/// Impl `<() as Foo>::g` has `#[ensures(Self::f() == ())]` and body `{}`.
/// The postcondition should be verified because Self::f() returns () (unit)
/// and the body returns () (unit), so Self::f() == () is trivially true.
///
/// In the real pipeline, `scope_logic_fn_modes` promotes `f` from Default
/// to Open when called from within the same trait impl scope, making `f`'s
/// defining axiom (`logic_f() = __trust_wp_unit`) visible. Without this
/// promotion (mode_overrides), `f` is opaque and the postcondition is
/// correctly unprovable. (#2676)
#[test]
#[timeout(30000)]
fn test_call_in_contract_self_f_with_logic_fn() {
    use trust_wp_core::{
        formula::ExprSort,
        logic::{LogicFnDef, LogicMode},
    };

    // Logic function f: body = () (unit), no params, no requires/ensures.
    // Mode is Default (bare `#[logic]`), but mode_overrides promotes to Open.
    let f_body = logic_fn_call("__trust_wp_tuple0", vec![]);
    let f_def = LogicFnDef::new("f".to_string(), "Foo::f".to_string(), vec![], f_body)
        .with_return_sort(Some(ExprSort::Unit));

    // Postcondition: Self::f() == ()
    let self_f = logic_fn_call("Self::f", vec![]);
    let unit_val = logic_fn_call("__trust_wp_tuple0", vec![]);
    let ensures = eq(self_f, unit_val);

    // Body: () (unit)
    let body = logic_fn_call("__trust_wp_tuple0", vec![]);

    // Mode overrides: promote f from Default to Open, simulating
    // scope_logic_fn_modes for same-module/same-trait-scope calls.
    let mode_overrides = [LogicMode::Open];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures])
            .return_expr(Some(&body))
            .logic_fns(Some(&[f_def]))
            .mode_overrides(Some(&mode_overrides)),
    )
    .expect("call_in_contract should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Self::f() == () should be verified when f is Open and returns unit: {result:?}"
    );
}
