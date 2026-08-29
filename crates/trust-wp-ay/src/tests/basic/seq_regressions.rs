// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
/// Regression for #1797: encoding `!(seq_eq)` must not add hidden top-level
/// equality assertions while building the subexpression.
#[test]
#[timeout(30000)]
fn test_negated_seq_eq_has_no_hidden_eq_side_effect_assertion() {
    let lhs = || view(var("a"));
    let rhs = || logic_fn_call("seq", vec![int(0), int(1), int(1), int(0)]);

    let mut encoder_not_eq = AYEncoder::new();
    let not_eq_expr = not(eq(lhs(), rhs()));
    encoder_not_eq.register_sort_hints(std::slice::from_ref(&not_eq_expr));
    let rev_before_not_eq = encoder_not_eq
        .assertion_pipeline_for_test()
        .assertion_revision();
    let not_eq_term = encoder_not_eq
        .encode_pure(&not_eq_expr)
        .expect("negated Seq equality should encode");
    let rev_after_not_eq = encoder_not_eq
        .assertion_pipeline_for_test()
        .assertion_revision();

    let mut encoder_ne = AYEncoder::new();
    let ne_expr = ne(lhs(), rhs());
    encoder_ne.register_sort_hints(std::slice::from_ref(&ne_expr));
    let rev_before_ne = encoder_ne
        .assertion_pipeline_for_test()
        .assertion_revision();
    let _ne_term = encoder_ne
        .encode_pure(&ne_expr)
        .expect("Seq inequality should encode");
    let rev_after_ne = encoder_ne
        .assertion_pipeline_for_test()
        .assertion_revision();

    let delta_not_eq = rev_after_not_eq.saturating_sub(rev_before_not_eq);
    let delta_ne = rev_after_ne.saturating_sub(rev_before_ne);
    assert_eq!(
        delta_not_eq, delta_ne,
        "encoding !(seq_eq) must have the same side-effect assertion footprint as seq_neq"
    );

    encoder_not_eq.assert_term(not_eq_term);
    let sat = encoder_not_eq.check_sat();
    assert!(
        matches!(sat, SolveResult::Sat),
        "negated Seq equality should be Sat, got {sat:?}"
    );
}

/// Regression for #1797: polarity must be preserved inside conditional contexts
/// such as `(!eq) || rhs`, with no hidden assertion side effects from `eq`.
#[test]
#[timeout(30000)]
fn test_disjunction_negated_seq_eq_preserves_polarity_without_side_effects() {
    let lhs = || view(var("a"));
    let rhs = || logic_fn_call("seq", vec![int(0), int(1), int(1), int(0)]);

    let mut encoder_not_eq = AYEncoder::new();
    let disjunction_not_eq = or(not(eq(lhs(), rhs())), gt(var("k"), int(0)));
    encoder_not_eq.register_sort_hints(std::slice::from_ref(&disjunction_not_eq));
    let rev_before_not_eq = encoder_not_eq
        .assertion_pipeline_for_test()
        .assertion_revision();
    let disjunction_term = encoder_not_eq
        .encode_pure(&disjunction_not_eq)
        .expect("disjunction with negated Seq equality should encode");
    let rev_after_not_eq = encoder_not_eq
        .assertion_pipeline_for_test()
        .assertion_revision();

    let mut encoder_ne = AYEncoder::new();
    let disjunction_ne = or(ne(lhs(), rhs()), gt(var("k"), int(0)));
    encoder_ne.register_sort_hints(std::slice::from_ref(&disjunction_ne));
    let rev_before_ne = encoder_ne
        .assertion_pipeline_for_test()
        .assertion_revision();
    let _disjunction_ne_term = encoder_ne
        .encode_pure(&disjunction_ne)
        .expect("disjunction with Seq inequality should encode");
    let rev_after_ne = encoder_ne
        .assertion_pipeline_for_test()
        .assertion_revision();

    let delta_not_eq = rev_after_not_eq.saturating_sub(rev_before_not_eq);
    let delta_ne = rev_after_ne.saturating_sub(rev_before_ne);
    assert_eq!(
        delta_not_eq, delta_ne,
        "encoding (!seq_eq)||rhs must have the same side-effect assertion footprint as (seq_neq)||rhs"
    );

    encoder_not_eq.assert_term(disjunction_term);

    // Force rhs false so satisfiability depends on the negated Seq equality branch.
    let rhs_false = encoder_not_eq
        .encode_pure(&le(var("k"), int(0)))
        .expect("k <= 0 should encode");
    encoder_not_eq.assert_term(rhs_false);

    let sat = encoder_not_eq.check_sat();
    assert!(
        matches!(sat, SolveResult::Sat),
        "(!seq_eq)||rhs with rhs forced false should be Sat, got {sat:?}"
    );
}

/// Regression for #1797: when both sides of a Seq equality have SeqValues
/// (from push_back encodings), encoding `!(a == b)` must NOT assert
/// component-wise `arr(a)==arr(b) && len(a)==len(b)` as a global side effect.
///
/// Uses `AYEncoder::new()` (with Array support) so that Seq methods register
/// SeqValues. The pure-mode tests above don't exercise this path because
/// `new_pure()` never registers SeqValues.
#[test]
#[timeout(30000)]
fn test_negated_seq_eq_both_seq_values_no_hidden_assertion() {
    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(std::time::Duration::from_millis(500)));

    // Build two distinct push_back chains that each register a SeqValue:
    //   a_pushed = a@.push_back(42)
    //   b_pushed = b@.push_back(99)
    let a_pushed = method_call(view(var("a")), "push_back", vec![int(42)]);
    let b_pushed = method_call(view(var("b")), "push_back", vec![int(99)]);

    // Register sort hints so the encoder knows a/b are Seq-sorted.
    let hint = eq(a_pushed.clone(), b_pushed.clone());
    encoder.register_sort_hints(std::slice::from_ref(&hint));

    // Encode both push_back expressions to register SeqValues for each.
    let a_term = encoder
        .encode_pure(&a_pushed)
        .expect("a push_back should encode");
    let b_term = encoder
        .encode_pure(&b_pushed)
        .expect("b push_back should encode");

    // Verify both sides have SeqValues registered.
    assert!(
        encoder.seq_state_for_test().has_seq_value(&a_term),
        "a_pushed should have a SeqValue"
    );
    assert!(
        encoder.seq_state_for_test().has_seq_value(&b_term),
        "b_pushed should have a SeqValue"
    );
    let a_value = encoder
        .seq_state_for_test()
        .get_seq_value(&a_term)
        .expect("a_pushed SeqValue should be present")
        .clone();
    let b_value = encoder
        .seq_state_for_test()
        .get_seq_value(&b_term)
        .expect("b_pushed SeqValue should be present")
        .clone();

    // Re-encoding the push_back operands legitimately emits their own
    // definitional axioms.  The forbidden side effect is narrower: a positive
    // equality between a's and b's concrete SeqValue components.  Build the
    // exact terms in both orientations so the regression checks that semantic
    // boundary directly instead of assuming that all encoding is assertion
    // free.
    let component_pairs = [
        (a_value.arr, b_value.arr),
        (a_value.len, b_value.len),
        (a_value.offset, b_value.offset),
    ];
    let mut forbidden_component_equalities = Vec::new();
    for (lhs, rhs) in component_pairs {
        forbidden_component_equalities.push(encoder.solver_mut().eq(lhs, rhs));
        forbidden_component_equalities.push(encoder.solver_mut().eq(rhs, lhs));
    }

    // Encode the NEGATED equality: !(a_pushed == b_pushed).
    // Before the #1797 fix, propagate_seq_value would assert arr/len/offset
    // equality as a global side effect when both sides had SeqValues.
    let not_eq = not(eq(a_pushed.clone(), b_pushed.clone()));
    encoder.register_sort_hints(std::slice::from_ref(&not_eq));
    let assertion_count_before_negated_encoding = encoder.solver().assertions().len();
    let not_eq_term = encoder
        .encode_pure(&not_eq)
        .expect("negated Seq equality should encode");
    let assertions = encoder.solver().assertions();
    let added_assertions = &assertions[assertion_count_before_negated_encoding..];
    for forbidden in forbidden_component_equalities {
        let forbidden_text = encoder.solver().format_term(forbidden);
        assert!(
            !added_assertions.iter().any(|assertion| {
                *assertion == forbidden
                    || encoder.solver().format_term(*assertion) == forbidden_text
            }),
            "encoding negated Seq equality injected forbidden positive component equality {forbidden_text}"
        );
    }

    // Assert the negated equality and check satisfiability.
    // With distinct push_back arguments (42 vs 99), the sequences differ,
    // so !(a_pushed == b_pushed) should be satisfiable.
    encoder.assert_term(not_eq_term);
    let result = encoder.check_sat();
    assert!(
        !result.is_unsat(),
        "negated Seq equality must not become contradictory; AY may conservatively return Unknown when its SAT model cannot evaluate auxiliary Seq axioms, got {result:?} (#1797)"
    );
}

/// Soundness regression for #1810: Seq Ne decomposition must NOT propagate
/// SeqValue from the known side to the unknown side.
///
/// The bug: `try_decompose_seq_equality` uses UF projectors (`seq_len`,
/// `seq_array`, `seq_offset`) for the side without a SeqValue. If
/// `propagate_seq_value` then copies the known side's concrete SeqValue
/// components to the unknown side, subsequent operations on that term
/// use the concrete components (fast-path) instead of the UF projectors
/// that appear in the decomposed Ne term. This disconnects the Ne
/// constraint from the concrete components, creating a soundness hole
/// where contradictory Ne assertions can be satisfied.
///
/// Test: after `a != push_back(b, 42)`, term `a` may have its own generic
/// Seq bridge, but it must not inherit the concrete components from
/// `push_back(b, 42)` (propagation was skipped for Ne).
#[test]
#[timeout(30000)]
fn test_seq_ne_does_not_propagate_seq_value() {
    let mut encoder = AYEncoder::new();

    // Build a push_back expression that registers a SeqValue for the result.
    let b_pushed = method_call(view(var("b")), "push_back", vec![int(42)]);
    let a_view = view(var("a"));

    // Register sort hints so encoder knows a and b are Seq-sorted.
    let hint = ne(a_view.clone(), b_pushed.clone());
    encoder.register_sort_hints(std::slice::from_ref(&hint));

    // Encode b.push_back(42) first to register its SeqValue.
    let b_term = encoder
        .encode_pure(&b_pushed)
        .expect("push_back should encode");
    assert!(
        encoder.seq_state_for_test().has_seq_value(&b_term),
        "b_pushed should have a SeqValue after encoding"
    );
    let b_seq_value = encoder
        .seq_state_for_test()
        .get_seq_value(&b_term)
        .expect("b_pushed SeqValue should be present")
        .clone();

    // Now encode `a != b.push_back(42)`.
    // Before #1810 fix, this would propagate b_pushed's SeqValue to a_view's
    // term, disconnecting UF projectors from the concrete components.
    let ne_expr = ne(a_view.clone(), b_pushed.clone());
    encoder.register_sort_hints(std::slice::from_ref(&ne_expr));
    let ne_term = encoder.encode_pure(&ne_expr).expect("Seq Ne should encode");

    // Key assertion: a's view term must not inherit b_pushed's concrete
    // components after Ne encoding. The decomposition used UF projectors for
    // a — propagating b's concrete components would disconnect those
    // projectors from the fast-path.
    let a_view_term = encoder.encode_pure(&a_view).expect("a view should encode");
    let a_seq_value = encoder
        .seq_state_for_test()
        .get_seq_value(&a_view_term)
        .expect("a view should have its own generic Seq bridge");
    assert_ne!(
        a_seq_value.arr, b_seq_value.arr,
        "Ne must NOT propagate the concrete array component to the unknown side (#1810)"
    );
    assert_ne!(
        a_seq_value.len, b_seq_value.len,
        "Ne must NOT propagate the concrete length component to the unknown side (#1810)"
    );

    // Smoke check: the Ne term is satisfiable (a can differ from b.push_back(42)).
    encoder.assert_term(ne_term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "Seq Ne should be Sat, got {result:?}"
    );
}

/// Regression: Ite branch sort propagation from Bool literal branches. (#544)
///
/// Reproduces traits/04.rs crash: `a.func1(b) && b.func2(a) && a.func3(b)`
/// where `&&` is MIR-desugared to nested Ite with `Bool(false)` else-branches.
/// The inner variables (`_call_0`, `_call_3`, `_call_6`) must be inferred as Bool
/// from the `Bool(false)` else-branch sort propagation.
///
/// Expression: `Ite(_call_3, Ite(_call_6, _call_0, false), false)`
///
/// Without this fix, `_call_0` defaulted to Int, causing
/// `mk_ite branches must have same sort, got Int vs Bool`.
#[test]
#[timeout(30000)]
fn test_ite_branch_bool_propagation_from_literal() {
    let mut encoder = AYEncoder::new_pure();

    // Simulates MIR-desugared `&&` chain: call1 && (call2 && call3)
    let body = ite(
        var("_call_3"),
        ite(var("_call_6"), var("_call_0"), bool_expr(false)),
        bool_expr(false),
    );

    encoder.register_sort_hints(std::slice::from_ref(&body));

    assert!(
        encoder.is_bool_var("_call_3"),
        "_call_3 should be Bool (Ite condition)"
    );
    assert!(
        encoder.is_bool_var("_call_6"),
        "_call_6 should be Bool (Ite condition)"
    );
    assert!(
        encoder.is_bool_var("_call_0"),
        "_call_0 should be Bool (Ite then-branch with Bool(false) else-branch)"
    );

    let term = encoder.encode_pure(&body);
    assert!(
        term.is_ok(),
        "Nested Ite with Bool(false) else-branches should encode without sort panic: {term:?}"
    );

    // Semantic: Ite(_call_3, Ite(_call_6, _call_0, false), false) is the MIR
    // desugaring of _call_3 && _call_6 && _call_0. Assert the result is true
    // and check SAT (all three calls can be true).
    let t = term.unwrap();
    encoder.assert_term(t);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Nested Ite (desugared &&) should be SAT when all calls are true"
    );
}
