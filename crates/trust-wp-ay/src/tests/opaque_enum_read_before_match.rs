// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A std `Option` read through its opaque annotation sort before a match
//! takes it apart is split by the phantom upgrade into two solver constants
//! (D-218): the premise constrains one, the arms read the other. A model of
//! such a query is not a counterexample, so the refutation is withheld, never
//! printed; the two constants are not linked, so nothing is proved either.

use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort, Pattern};

use super::{super::*, helpers::*};

fn opaque(name: &str, family: &str) -> PureExpr {
    var_with_sort(name, ExprSort::Datatype(intern_sort_name(family)))
}

fn ctor(name: &str, payload: bool) -> Pattern {
    Pattern::Constructor {
        name: name.to_string(),
        inner: payload.then(|| Box::new(Pattern::Wildcard)),
    }
}

/// `match scrutinee { taken(..) => true, other(..) => false }`.
fn arm_test(scrutinee: PureExpr, taken: (&str, bool), other: (&str, bool)) -> PureExpr {
    match_expr(
        scrutinee,
        vec![
            (ctor(taken.0, taken.1), bool_expr(true)),
            (ctor(other.0, other.1), bool_expr(false)),
        ],
    )
}

fn verify(requires: &[PureExpr], ensures: PureExpr) -> VerificationResult {
    verify_function_with_modes(VerificationRequest::new(requires, &[ensures]))
        .expect("the contract encodes")
}

/// The true contract: the split leaves the premise unread by the arms, and
/// the model that sets them apart is not published.
#[test]
#[timeout(60000)]
fn option_is_some_premise_then_match_is_withheld_not_refuted() {
    let x = opaque("x", "std::option::Option");
    let result = verify(
        &[method_call(x.clone(), "is_some", vec![])],
        arm_test(x, ("Some", true), ("None", false)),
    );
    assert!(
        crate::is_withheld_refutation(&result),
        "a model over a split `x` is not a counterexample: {result:?}"
    );
}

/// The false twin: withheld as well, and never credited.
#[test]
#[timeout(60000)]
fn option_is_some_premise_with_the_other_arm_claimed_is_not_verified() {
    let x = opaque("x", "std::option::Option");
    let result = verify(
        &[method_call(x.clone(), "is_some", vec![])],
        arm_test(x, ("None", false), ("Some", true)),
    );
    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "the fail-safe withholds refutations only: {result:?}"
    );
}

/// The D-169 shape: the second call's postcondition is a premise scoped to
/// the edge `$call_4.is_some()` of the first, and the first call's own
/// postcondition matches `$call_4`. The edge reads the opaque constant and the
/// match the upgraded one, so the solver refutes the goal by leaving the edge
/// false; that model is withheld.
#[test]
#[timeout(60000)]
fn call_result_switch_edge_then_match_is_not_refuted() {
    let first = opaque("$call_4", "std::option::Option");
    let second = opaque("$call_8", "std::option::Option");
    let edge = method_call(first.clone(), "is_some", vec![]);
    let requires = [
        arm_test(first.clone(), ("Some", true), ("None", false)),
        implies(
            edge.clone(),
            arm_test(second.clone(), ("None", false), ("Some", true)),
        ),
    ];
    let goal = and(edge, method_call(second, "is_none", vec![]));
    let result = verify(&requires, goal);
    assert!(
        !matches!(result, VerificationResult::Failed(_)),
        "the edge and the first call's postcondition read two constants: {result:?}"
    );
}

/// The split is the condition, not the upgrade: a match on an `Option` no
/// premise read before it keeps its refutation.
#[test]
#[timeout(60000)]
fn option_match_with_no_earlier_read_is_still_refuted() {
    let x = opaque("x", "std::option::Option");
    let result = verify(&[], arm_test(x, ("Some", true), ("None", false)));
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "no assertion read the abandoned constant: {result:?}"
    );
}
