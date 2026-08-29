// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

/// Regression test for #585: Bool sort hint on Int-returning logic function
/// causes `mk_eq(Bool, Int)` panic when compared with integer literal.
///
/// Scenario: `size_of_logic()` returns Int, but if it appears in a Bool-requiring
/// context (e.g., `!size_of_logic() && ...`) in one expression, and then
/// `size_of_logic() == 1` in another, the Bool sort hint from the first
/// expression contaminates the placeholder declaration, causing `mk_eq(Bool, Int)`.
/// Semantic check: size_of_logic() == 1 is satisfiable (UF unconstrained).
/// Part of #1990.
#[test]
#[timeout(30000)]
fn test_placeholder_logic_fn_wrong_bool_hint_eq_int_no_panic() {
    let mut encoder = AYEncoder::new();

    // First expression: size_of_logic() in a Bool-requiring context.
    // Not(LogicFnCall) tells the sort hint system the function returns Bool.
    let bool_ctx_expr = not(logic_fn_call("size_of_logic", vec![]));

    // Register sort hints — this will mark logic_size_of_logic as Bool
    encoder.register_sort_hints(std::slice::from_ref(&bool_ctx_expr));

    // Second expression: size_of_logic() == 1
    // The function actually returns Int, but the sort hint says Bool.
    let eq_expr = eq(logic_fn_call("size_of_logic", vec![]), int(1));

    let term = encoder
        .encode_pure(&eq_expr)
        // Before fix: panics with "BUG: mk_eq expects same sort, got Bool = Int"
        // After fix: should succeed (placeholder respects Eq context over stale hint)
        .expect("size_of_logic() == 1 with wrong Bool hint should not panic");

    // Semantic: size_of_logic() == 1 is satisfiable (UF is unconstrained)
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "size_of_logic() == 1 is satisfiable (unconstrained UF) (#1990)"
    );
}

/// Regression guard for mixed-sort placeholder reuse:
/// a nullary placeholder first declared as Int must not later crash
/// when the same name is used in Bool equality. This is the same
/// shape as `Default::default()` appearing in multiple `mem::take`
/// postconditions with different monomorphized `T`s. (#2169 audit)
#[test]
#[timeout(30000)]
fn test_placeholder_nullary_logic_fn_int_decl_then_bool_eq_no_panic() {
    let mut encoder = AYEncoder::new();

    let int_eq = eq(logic_fn_call("Default::default", vec![]), int(0));
    encoder
        .encode_pure(&int_eq)
        .expect("Default::default() == 0 should declare an Int placeholder");

    let bool_eq = eq(logic_fn_call("Default::default", vec![]), bool_expr(true));
    encoder.encode_pure(&bool_eq).expect(
        "reusing a nullary placeholder in Bool equality after Int declaration \
         should not panic",
    );
}

/// Regression guard for the opposite order: a Bool use must not lock a
/// nullary placeholder to Bool and then crash when the same name is later
/// used in Int equality. Mirrors mixed `mem::take::<bool>` / `::<i32>`
/// postconditions in one query. (#2169 audit)
#[test]
#[timeout(30000)]
fn test_placeholder_nullary_logic_fn_bool_decl_then_int_eq_no_panic() {
    let mut encoder = AYEncoder::new();

    let bool_eq = eq(logic_fn_call("Default::default", vec![]), bool_expr(true));
    encoder
        .encode_pure(&bool_eq)
        .expect("Default::default() == true should declare a Bool placeholder");

    let int_eq = eq(logic_fn_call("Default::default", vec![]), int(0));
    encoder.encode_pure(&int_eq).expect(
        "reusing a nullary placeholder in Int equality after Bool declaration \
         should not panic",
    );
}

/// Regression guard for mixed-sort placeholder reuse beyond the nullary
/// case: a non-nullary placeholder first declared as Int-returning must not
/// later crash when the same source name is used in Bool equality. (#2169 audit)
#[test]
#[timeout(30000)]
fn test_placeholder_unary_logic_fn_int_decl_then_bool_eq_no_panic() {
    let mut encoder = AYEncoder::new();

    let int_eq = eq(logic_fn_call("ambiguous_placeholder", vec![int(0)]), int(1));
    encoder
        .encode_pure(&int_eq)
        .expect("ambiguous_placeholder(0) == 1 should declare an Int-return placeholder");

    let bool_eq = eq(
        logic_fn_call("ambiguous_placeholder", vec![int(0)]),
        bool_expr(true),
    );
    encoder.encode_pure(&bool_eq).expect(
        "reusing a unary placeholder in Bool equality after Int declaration \
         should not panic",
    );
}

/// Regression guard for the reverse mixed-sort order on non-nullary
/// placeholders: a Bool-returning first use must not lock a later Int
/// equality to the wrong return sort. (#2169 audit)
#[test]
#[timeout(30000)]
fn test_placeholder_unary_logic_fn_bool_decl_then_int_eq_no_panic() {
    let mut encoder = AYEncoder::new();

    let bool_eq = eq(
        logic_fn_call("ambiguous_placeholder", vec![int(0)]),
        bool_expr(true),
    );
    encoder
        .encode_pure(&bool_eq)
        .expect("ambiguous_placeholder(0) == true should declare a Bool-return placeholder");

    let int_eq = eq(logic_fn_call("ambiguous_placeholder", vec![int(0)]), int(1));
    encoder.encode_pure(&int_eq).expect(
        "reusing a unary placeholder in Int equality after Bool declaration \
         should not panic",
    );
}

/// Test placeholder declaration (unregistered function) with Bool arg infers Bool sort.
///
/// Semantic: UF congruence — unknown_pred(x>0) called twice with same args must be equal.
/// Part of #1990.
#[test]
#[timeout(30000)]
fn test_placeholder_logic_fn_bool_arg_infers_sort() {
    let mut encoder = AYEncoder::new();

    // Call an unregistered function with a Bool argument — should create placeholder
    // with Bool param sort instead of Int (thanks to infer_expr_sort on args).
    let expr = logic_fn_call("unknown_pred", vec![gt(var("x"), int(0))]);

    let term1 = encoder
        .encode_pure(&expr)
        .expect("placeholder with Bool arg should encode without sort panic");

    // UF congruence: same placeholder call must produce equal terms
    let expr2 = logic_fn_call("unknown_pred", vec![gt(var("x"), int(0))]);
    let term2 = encoder
        .encode_pure(&expr2)
        .expect("second placeholder encode");
    let eq = encoder.solver.eq(term1, term2);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unknown_pred(x>0) != unknown_pred(x>0) should be Unsat (UF congruence) (#1990)"
    );
}

/// Regression follow-up for #1128: placeholder logic-function calls must
/// use the encoded argument sort for View(Var(_)) receivers.
#[test]
#[timeout(30000)]
fn test_placeholder_logic_fn_seq_view_arg_no_sort_mismatch() {
    let mut encoder = AYEncoder::new();

    // push_back tags v_view as Seq in sort hints.
    let hint_expr = method_call(view(var("v")), "push_back", vec![int(0)]);
    encoder.register_sort_hints(&[hint_expr]);

    // Before the fix, apply_logic_fn inferred Int from View(...) and panicked
    // when applying the placeholder UF to the Seq-sorted argument term.
    // NOTE: encoding-only — tests Seq sort propagation for placeholder UFs.
    // check_sat would test unconstrained UF semantics, not the sort fix. See #1990.
    let expr = logic_fn_call("unknown_logic_fn", vec![view(var("v"))]);
    encoder
        .encode_pure(&expr)
        .expect("placeholder logic fn on Seq-sorted View arg should not panic");
}

/// Regression: pearlite!{ expr } should be unwrapped at parse time (#610).
///
/// Before the fix, `pearlite!{ x == x }` was parsed as
/// `LogicFnCall { "pearlite", [BinOp(Eq, Var("x"), Var("x"))] }` which
/// caused a Bool/Int sort mismatch when used in logic function bodies:
/// - The function was declared with Bool return sort (from formula hints)
/// - But the body encoded `pearlite(x == x)` as Int (placeholder default)
/// - `solver.eq(Bool, Int)` panicked in the defining axiom
///
/// The fix unwraps `pearlite!` at parse time, so the body is just
/// `BinOp(Eq, Var("x"), Var("x"))` — a Bool expression that matches the
/// declared return sort.
#[test]
#[timeout(30000)]
fn test_logic_fn_with_pearlite_body_no_sort_mismatch() {
    use crate::{verify_function_with_modes, VerificationRequest};

    // reflexive(x) = x == x  (pearlite! unwrapped at parse time)
    let reflexive_fn = LogicFnDef::new(
        "reflexive".to_string(),
        "test::reflexive".to_string(),
        vec!["x".to_string()],
        eq(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    let logic_fns = vec![reflexive_fn];

    // #[ensures(reflexive(result))]
    let ensures = vec![logic_fn_call("reflexive", vec![var("result")])];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).logic_fns(Some(&logic_fns)),
    )
    .expect("logic fn with pearlite-unwrapped body should not panic");
    // reflexive(x) = (x == x) is always true, so ensures(reflexive(result)) should verify.
    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "ensures(reflexive(result)) should verify: {result:?}"
    );
}
