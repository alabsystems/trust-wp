// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use ay_dpll::api::{Term, TermKind};
use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use super::verify_mut_borrow_function_with_modes;
use crate::{
    encoder::AYEncoder,
    tests::helpers::{
        and, bool_expr, deref, eq, exists_with_sort, forall_with_sort, gt, int, logic_fn_call, var,
    },
    verify::{encode_negated_postcondition, types::MutBorrowRequest, ResolveContinuation},
    VerificationResult,
};

fn term_contains_quantifier(encoder: &AYEncoder, term: Term) -> bool {
    match encoder.solver().term_kind(term) {
        TermKind::Forall | TermKind::Exists => true,
        _ => encoder
            .solver()
            .term_children(term)
            .into_iter()
            .any(|child| term_contains_quantifier(encoder, child)),
    }
}

/// Shared-helper regression (#2365): a witnessed existential that simplifies to
/// `true` should negate directly to `false`, not keep a redundant quantified OR.
#[test]
#[timeout(30000)]
fn shared_negation_helper_short_circuits_unit_existential_to_false() {
    let ensure = exists_with_sort("_u", ExprSort::Unit, bool_expr(true));
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let negated = encode_negated_postcondition(&mut encoder, &ensure, None, None)
        .expect("unit existential should encode");

    assert_eq!(
        negated,
        encoder.solver_mut().bool_const(false),
        "shared negation helper should collapse a witnessed unit existential to false"
    );
}

/// Smoke coverage: a simple existential mut_borrow postcondition remains
/// verifiable after shared negation routing.
#[test]
#[timeout(30000)]
fn existential_negation_smoke_verifies() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let ensures = vec![exists_with_sort("y", ExprSort::Int, gt(var("y"), int(0)))];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "simple existential should still verify in mut_borrow: {result:?}"
    );
}

/// Gap 7 regression (#2365): universal postconditions with Open-mode logic
/// functions need the shared Skolemized negation path in mut_borrow.
#[test]
#[timeout(30000)]
fn open_logic_universal_postcondition_skolemizes() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let identity_fn = LogicFnDef::new(
        "id".to_string(),
        "test::id".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let body = deref(var("v"));
    let ensures = vec![forall_with_sort(
        "y",
        ExprSort::Int,
        eq(logic_fn_call("id", vec![var("y")]), var("y")),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&identity_fn))),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Open-mode universal should use Skolemized negation in mut_borrow: {result:?}"
    );
}

/// Structural regression (#2365): the mut_borrow obligation path must assert a
/// Skolemized ground negation for Open-mode universals, not a quantified ay
/// negation. This catches the old pre-helper path, where the first assertion
/// was `not(forall ...)` and no `sk_*` constant was introduced.
#[test]
#[timeout(30000)]
fn mut_borrow_obligation_grounds_open_logic_universal_negation() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    use super::{
        super::solver_tail::ObligationSliceContext,
        obligation::verify_mut_borrow_single_obligation_slice,
    };

    let identity_fn = LogicFnDef::new(
        "id".to_string(),
        "test::id".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);

    let ensures = [forall_with_sort(
        "y",
        ExprSort::Int,
        eq(logic_fn_call("id", vec![var("y")]), var("y")),
    )];

    let mut structural_encoder = AYEncoder::new_pure_with_quantifiers();
    structural_encoder
        .register_logic_fn(&identity_fn)
        .expect("logic fn registration should succeed");
    let negated = encode_negated_postcondition(
        &mut structural_encoder,
        &ensures[0],
        Some(std::slice::from_ref(&identity_fn)),
        None,
    )
    .expect("Skolemized mut_borrow negation should encode");
    assert!(
        !term_contains_quantifier(&structural_encoder, negated),
        "Skolemized mut_borrow negation should stay ground after helper encoding"
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder
        .register_logic_fn(&identity_fn)
        .expect("logic fn registration should succeed");

    let ctx = ObligationSliceContext {
        all_ensures: &ensures,
        requires: &[],
        logic_fns: Some(std::slice::from_ref(&identity_fn)),
        mode_overrides: None,
        type_invariants: None,
        return_expr: None,
        mut_borrow_final_values: None,
        mutation_continued_params: None,
        body_div_obligations: &[],
        fresh_base_recheck: None,
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };

    let result = verify_mut_borrow_single_obligation_slice(&mut encoder, &ensures[0], &ctx)
        .expect("mut_borrow obligation encoding should succeed");

    assert!(
        matches!(result, ResolveContinuation::Continue(_)),
        "Open-mode universal obligation should encode and solve cleanly: {result:?}"
    );
}

/// Gap 7 regression (#2365): embedded existentials should be instantiated with
/// body-derived witnesses before negation in the mut_borrow path.
#[test]
#[timeout(30000)]
fn embedded_existential_uses_body_witness() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let return_expr = logic_fn_call("Some", vec![int(42)]);
    let ensures = vec![and(
        eq(var("result"), logic_fn_call("Some", vec![int(42)])),
        exists_with_sort(
            "y",
            ExprSort::Int,
            and(
                eq(var("result"), logic_fn_call("Some", vec![var("y")])),
                gt(var("y"), int(0)),
            ),
        ),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "embedded existential should use body witness in mut_borrow: {result:?}"
    );
}

/// Structural regression (#2365): the first mut_borrow negated obligation for
/// an embedded existential should be ground after body-witness instantiation.
/// The old path asserted `not(and(... exists ...))`, leaving the existential
/// inside the first solver assertion.
#[test]
#[timeout(30000)]
fn mut_borrow_obligation_eliminates_embedded_existential_from_first_assertion() {
    use super::{
        super::solver_tail::ObligationSliceContext,
        obligation::verify_mut_borrow_single_obligation_slice,
    };

    let return_expr = logic_fn_call("Some", vec![int(42)]);
    let ensures = [and(
        eq(var("result"), logic_fn_call("Some", vec![int(42)])),
        exists_with_sort(
            "y",
            ExprSort::Int,
            and(
                eq(var("result"), logic_fn_call("Some", vec![var("y")])),
                gt(var("y"), int(0)),
            ),
        ),
    )];

    let mut structural_encoder = AYEncoder::new_pure_with_quantifiers();
    let negated = encode_negated_postcondition(
        &mut structural_encoder,
        &ensures[0],
        None,
        Some(&return_expr),
    )
    .expect("mut_borrow embedded existential negation should encode");
    assert!(
        !term_contains_quantifier(&structural_encoder, negated),
        "embedded existential should be eliminated from the mut_borrow negated goal"
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let ctx = ObligationSliceContext {
        all_ensures: &ensures,
        requires: &[],
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        return_expr: Some(&return_expr),
        mut_borrow_final_values: None,
        mutation_continued_params: None,
        body_div_obligations: &[],
        fresh_base_recheck: None,
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };

    let result = verify_mut_borrow_single_obligation_slice(&mut encoder, &ensures[0], &ctx)
        .expect("mut_borrow embedded existential encoding should succeed");

    assert!(
        matches!(result, ResolveContinuation::Continue(_)),
        "embedded existential obligation should encode and solve cleanly: {result:?}"
    );
}
