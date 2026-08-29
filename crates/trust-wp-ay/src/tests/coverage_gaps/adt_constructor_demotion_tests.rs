// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for ADT constructor sort inference non-demotion (#1474, bug/1504).
//!
//! Standard ADT constructors (Some/None/Ok/Err) encoded as `PureExpr::LogicFnCall`
//! must NOT trigger the demoting `SortFallbackToIntFromLogicFn` counter.
//! These constructors return `Sort::Int` in the UF encoding path, so the Int
//! fallback is semantically correct — the counter is a false positive that
//! converts Verified to Unknown via unsoundness demotion.
//!
//! The fix is in `infer_encoded_sort` (method_call/mod.rs): known ADT
//! constructor names return `Sort::Int` directly before reaching the
//! AST-level catch-all that fires the demoting counter.

use ntest::timeout;

use super::*;
use crate::{
    encoder::unsoundness::{self, UnsoundnessCategory},
    verify_function_with_modes, VerificationRequest,
};

/// `Some(true)` as a return expression should not fire the demoting counter.
///
/// This is the motivating case from `bug/1504.rs`:
///   ensures: match result { Some(true) => true, _ => false }
///   body: Some(true)
///
/// Without the fix, the `Some` LogicFnCall in the body hits the catch-all
/// in `infer_expr_sort_impl` which increments `SortFallbackToIntFromLogicFn`.
/// The demotion then converts Verified to Unknown. (#1474)
#[test]
#[timeout(30000)]
fn some_true_body_does_not_fire_demotion_counter() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    // Body: Some(true)
    let body = logic_fn_call("Some", vec![bool_expr(true)]);

    // Postcondition: match result { Some(true) => true, _ => false }
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Literal(bool_expr(true)))),
                },
                bool_expr(true),
            ),
            (Pattern::Wildcard, bool_expr(false)),
        ],
    )];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    );

    // The verification should complete without error.
    assert!(
        result.is_ok(),
        "Some(true) with match postcondition should not error: {result:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    let fallback_count = delta
        .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
        .copied()
        .unwrap_or(0);
    assert_eq!(
        fallback_count, 0,
        "ADT constructor Some should NOT increment SortFallbackToIntFromLogicFn. \
         Delta: {delta:?}"
    );

    unsoundness::reset();
}

/// `None` as a return expression should not fire the demoting counter.
///
/// None is a zero-arg ADT constructor: LogicFnCall { name: "None", args: [] }.
/// The same fix intercepts it in `infer_encoded_sort`. (#1474)
#[test]
#[timeout(30000)]
fn none_body_does_not_fire_demotion_counter() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    // Body: None
    let body = logic_fn_call("None", vec![]);

    // Postcondition: match result { None => true, _ => false }
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                bool_expr(true),
            ),
            (Pattern::Wildcard, bool_expr(false)),
        ],
    )];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    );

    assert!(
        result.is_ok(),
        "None with match postcondition should not error: {result:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    let fallback_count = delta
        .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
        .copied()
        .unwrap_or(0);
    assert_eq!(
        fallback_count, 0,
        "ADT constructor None should NOT increment SortFallbackToIntFromLogicFn. \
         Delta: {delta:?}"
    );

    unsoundness::reset();
}

/// `Ok(x)` as a return expression should not fire the demoting counter.
#[test]
#[timeout(30000)]
fn ok_constructor_does_not_fire_demotion_counter() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let body = logic_fn_call("Ok", vec![int(42)]);
    let ensures = vec![eq(var("result"), int(42))];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    );

    assert!(result.is_ok(), "Ok(42) should not error: {result:?}");

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    let fallback_count = delta
        .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
        .copied()
        .unwrap_or(0);
    assert_eq!(
        fallback_count, 0,
        "ADT constructor Ok should NOT increment SortFallbackToIntFromLogicFn. \
         Delta: {delta:?}"
    );

    unsoundness::reset();
}

/// `Err(1)` as a return expression should not fire the demoting counter.
#[test]
#[timeout(30000)]
fn err_constructor_does_not_fire_demotion_counter() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let body = logic_fn_call("Err", vec![int(1)]);
    let ensures = vec![eq(var("result"), int(1))];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    );

    assert!(result.is_ok(), "Err(1) should not error: {result:?}");

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    let fallback_count = delta
        .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
        .copied()
        .unwrap_or(0);
    assert_eq!(
        fallback_count, 0,
        "ADT constructor Err should NOT increment SortFallbackToIntFromLogicFn. \
         Delta: {delta:?}"
    );

    unsoundness::reset();
}
