// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// Test encoding of `Vec::push` postcondition: (^self)@ == `self@.push_back(v)`
///
/// This is the key contract from crates/trust-wp-std/src/std/vec.rs:68
/// The verification approach:
/// 1. Assume the function body semantically performs `push_back`
/// 2. Assert that the postcondition holds
/// 3. UNSAT means the postcondition is verified
#[test]
#[timeout(30000)]
fn test_vec_push_postcondition_encodes() {
    let mut encoder = AYEncoder::new();

    // Build the postcondition: (^self)@ == self@.push_back(v)
    // - (^self)@ is Final(View(Var("self")))
    // - self@ is View(Var("self"))
    // - self@.push_back(v) is MethodCall on self@ with arg v

    // Left side: (^self)@ - the final view of the Vec
    let final_view = view(final_expr(var("self")));

    // Right side: self@.push_back(v)
    let old_view = view(var("self"));
    let push_back_result = method_call(old_view, "push_back", vec![var("v")]);

    // Postcondition: (^self)@ == self@.push_back(v)
    let postcond = eq(final_view, push_back_result);

    // Encode the postcondition
    let result = encoder.encode_pure(&postcond);
    assert!(
        result.is_ok(),
        "Vec::push postcondition should encode successfully: {result:?}"
    );

    // Verify that appropriate variables were created
    assert!(
        encoder.vars_for_test().contains_key("self_view"),
        "Should create self_view for self@"
    );
    assert!(
        encoder.vars_for_test().contains_key("final_self_view"),
        "Should create final_self_view for (^self)@"
    );
    assert!(
        encoder.vars_for_test().contains_key("v"),
        "Should create v variable for push argument"
    );

    // Semantic: postcondition is a satisfiable Bool equality (not vacuously false).
    // Full verification is in test_vec_push_verification_complete (companion test).
    let term = result.unwrap();
    encoder.assert_term(term);
    let push_result = encoder.check_sat();
    assert!(
        matches!(push_result, SolveResult::Sat),
        "Vec::push postcondition should be Sat, got {push_result:?}"
    );
    assert!(
        encoder
            .last_solve_evidence()
            .is_some_and(|evidence| evidence.model_validated && evidence.accepted_for_consumer),
        "positive temporal Seq equality must have a consumer-accepted, validated model"
    );

    // Verify postcondition is not a tautology: its negation should also be SAT
    // (meaning the encoded formula actually constrains variable assignments).
    let mut encoder2 = AYEncoder::new();
    let postcond2 = eq(
        view(final_expr(var("self"))),
        method_call(view(var("self")), "push_back", vec![var("v")]),
    );
    let term2 = encoder2
        .encode_pure(&postcond2)
        .expect("postcond should re-encode");
    let neg = encoder2.solver.not(term2);
    encoder2.assert_term(neg);
    let neg_result = encoder2.check_sat();
    assert!(
        matches!(neg_result, SolveResult::Sat),
        "NOT(postcondition) should be Sat — postcondition is contingent, got {neg_result:?}"
    );
    assert!(
        encoder2
            .last_solve_evidence()
            .is_some_and(|evidence| evidence.model_validated && evidence.accepted_for_consumer),
        "negative temporal Seq equality must have a consumer-accepted, validated model"
    );
}

/// Test that `Vec::len` contract encodes correctly
///
/// Contract: ensures result@ == `self@.len()`
#[test]
#[timeout(30000)]
fn test_vec_len_postcondition_encodes() {
    let mut encoder = AYEncoder::new();

    // result == self@.len()
    let self_view = view(var("self"));
    let len_call = method_call(self_view, "len", vec![]);

    let postcond = eq(var("result"), len_call);

    let term = encoder
        .encode_pure(&postcond)
        .expect("Vec::len postcondition should encode");

    // Semantic: postcondition is a satisfiable Bool — there exists an assignment
    // where result equals self@.len() (trivially true for UFs, but verifies
    // the encoding produces a well-sorted Bool, not an Int or sort error).
    encoder.assert_term(term);
    let len_result = encoder.check_sat();
    assert!(
        matches!(len_result, SolveResult::Sat),
        "Vec::len postcondition should be Sat, got {len_result:?}"
    );

    // Verify postcondition is contingent: its negation should also be Sat.
    let mut encoder2 = AYEncoder::new();
    let postcond2 = eq(var("result"), method_call(view(var("self")), "len", vec![]));
    let term2 = encoder2
        .encode_pure(&postcond2)
        .expect("postcond should re-encode");
    let neg = encoder2.solver.not(term2);
    encoder2.assert_term(neg);
    let neg_len_result = encoder2.check_sat();
    assert!(
            matches!(neg_len_result, SolveResult::Sat),
            "NOT(result == self@.len()) should be Sat — postcondition is contingent, got {neg_len_result:?}"
        );
}

/// Test full `Vec::push` verification with body semantics
///
/// This test verifies that when the function body implements `push_back`,
/// the postcondition (^self)@ == `self@.push_back(v)` is provably satisfied.
#[test]
#[timeout(30000)]
fn test_vec_push_verification_complete() {
    let mut encoder = AYEncoder::new();

    // Setup: The function body semantically performs:
    //   final_self_view = seq_push_back(self_view, v)
    //
    // We model this by asserting the body effect, then checking
    // that the postcondition is satisfiable (or that its negation is UNSAT).

    // 1. Encode the body effect as an equality:
    //    final_self@ = self@.push_back(v)
    let old_view = view(var("self"));
    let v_expr = var("v");
    let push_back_expr = method_call(old_view.clone(), "push_back", vec![v_expr]);

    let final_view = view(final_expr(var("self")));

    // Body effect: final_self_view = push_back(self_view, v)
    let body_effect = eq(final_view.clone(), push_back_expr.clone());

    let body_term = encoder
        .encode_pure(&body_effect)
        .expect("Body effect should encode");
    encoder.assert_term(body_term);

    // 2. Postcondition: (^self)@ == self@.push_back(v)
    //    This is the same as the body effect, so should be trivially true
    let postcond = eq(final_view, push_back_expr);

    let postcond_term = encoder
        .encode_pure(&postcond)
        .expect("Postcond should encode");
    assert_eq!(
        body_term, postcond_term,
        "the same temporal Seq assignment must reuse one stable certified monitor"
    );
    assert!(
        encoder
            .solver
            .format_term(postcond_term)
            .starts_with("seq_temporal_equality_monitor_"),
        "symbolic temporal push-back equality should use its certified monitor"
    );

    // 3. To verify: assert NOT(postcond) and check UNSAT
    let neg_postcond = encoder.solver.not(postcond_term);
    encoder.assert_term(neg_postcond);

    // UNSAT means the postcondition is verified
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Vec::push postcondition should verify (expected UNSAT, got {result:?})"
    );
}

/// The temporal monitor is an abstraction boundary, not an unconstrained
/// verification oracle: a positive monitor must imply the native Seq-carrier
/// identity it represents.
#[test]
#[timeout(30000)]
fn test_vec_push_temporal_monitor_certifies_native_identity() {
    let mut encoder = AYEncoder::new();
    let final_view = view(final_expr(var("self")));
    let push_back_expr = method_call(view(var("self")), "push_back", vec![var("v")]);
    let postcond = eq(final_view.clone(), push_back_expr.clone());

    let monitor = encoder
        .encode_pure(&postcond)
        .expect("temporal push-back equality should encode");
    let final_term = encoder
        .encode_pure(&final_view)
        .expect("temporal final view should encode");
    let push_back_term = encoder
        .encode_pure(&push_back_expr)
        .expect("push-back expression should encode");
    let native_identity = encoder.solver.eq(final_term, push_back_term);
    let violates_certificate = encoder.solver.not(native_identity);

    encoder.assert_term(monitor);
    encoder.assert_term(violates_certificate);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "positive temporal monitor with a false native identity must be UNSAT, got {result:?}"
    );
}

/// A positive temporal monitor must also certify the observable Seq
/// decomposition. This is distinct from native-carrier identity: normalized
/// temporal views can have separate carrier terms whose registered components
/// are the semantic bridge used by downstream length/index consumers.
#[test]
#[timeout(30000)]
fn test_vec_push_temporal_monitor_certifies_observable_length() {
    let mut encoder = AYEncoder::new();
    let final_view = view(final_expr(var("self")));
    let push_back_expr = method_call(view(var("self")), "push_back", vec![var("v")]);
    let postcond = eq(final_view.clone(), push_back_expr.clone());

    let monitor = encoder
        .encode_pure(&postcond)
        .expect("temporal push-back equality should encode");
    let final_term = encoder
        .encode_pure(&final_view)
        .expect("temporal final view should encode");
    let push_back_term = encoder
        .encode_pure(&push_back_expr)
        .expect("push-back expression should encode");
    let final_len = encoder
        .seq_len_term(final_term)
        .expect("temporal final carrier length should encode");
    let push_back_len = encoder
        .seq_len_term(push_back_term)
        .expect("push-back carrier length should encode");
    let same_len = encoder.solver.eq(final_len, push_back_len);
    let violates_certificate = encoder.solver.not(same_len);

    encoder.assert_term(monitor);
    encoder.assert_term(violates_certificate);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "positive temporal monitor with differing observable lengths must be UNSAT, got {result:?}"
    );
}
/// The converse is intentionally absent: a false temporal monitor must leave
/// the represented Seq carriers free to differ, including at an observable
/// length projection. The control uses the authenticated `seq_len_term`
/// projections of the exact native carrier terms: spelling a native Seq
/// disequality directly is currently outside AY's complete model-validation
/// lane and conservatively returns `Unknown(Incomplete)`, whereas differing
/// observable lengths establish the semantic distinction we need.
#[test]
#[timeout(30000)]
fn test_vec_push_negative_temporal_monitor_preserves_disequality_model() {
    let mut encoder = AYEncoder::new();
    let final_view = view(final_expr(var("self")));
    let push_back_expr = method_call(view(var("self")), "push_back", vec![var("v")]);
    let postcond = eq(final_view.clone(), push_back_expr.clone());

    let monitor = encoder
        .encode_pure(&postcond)
        .expect("temporal push-back equality should encode");
    let final_term = encoder
        .encode_pure(&final_view)
        .expect("temporal final view should encode");
    let push_back_term = encoder
        .encode_pure(&push_back_expr)
        .expect("push-back expression should encode");
    let final_len = encoder
        .seq_len_term(final_term)
        .expect("temporal final carrier length should encode");
    let push_back_len = encoder
        .seq_len_term(push_back_term)
        .expect("push-back carrier length should encode");
    let same_len = encoder.solver.eq(final_len, push_back_len);
    let differing_len = encoder.solver.not(same_len);

    let negative_monitor = encoder.solver.not(monitor);
    encoder.assert_term(negative_monitor);
    encoder.assert_term(differing_len);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "negative temporal monitor must preserve a model with differing observable lengths, got {result:?}"
    );
    assert!(
        encoder
            .last_solve_evidence()
            .is_some_and(|evidence| evidence.model_validated && evidence.accepted_for_consumer),
        "negative temporal monitor must preserve a consumer-accepted, validated differing-length model"
    );
}

/// Test `Vec::new` postcondition: `result@.len()` == 0
#[test]
#[timeout(30000)]
fn test_vec_new_postcondition_encodes() {
    let mut encoder = AYEncoder::new();

    // result@.len() == 0
    let result_view = view(var("result"));
    let len_call = method_call(result_view, "len", vec![]);

    let postcond = eq(len_call, int(0));

    let term = encoder
        .encode_pure(&postcond)
        .expect("Vec::new postcondition should encode");

    // Semantic: the encoded equality is satisfiable (a model exists where
    // result@.len() == 0 holds — verifies the encoding is a well-sorted Bool).
    encoder.assert_term(term);
    let new_result = encoder.check_sat();
    assert!(
        matches!(new_result, SolveResult::Sat),
        "Vec::new postcondition should be Sat, got {new_result:?}"
    );

    // Verify postcondition is contingent: its negation should also be Sat.
    let mut encoder2 = AYEncoder::new();
    let postcond2 = eq(method_call(view(var("result")), "len", vec![]), int(0));
    let term2 = encoder2
        .encode_pure(&postcond2)
        .expect("postcond should re-encode");
    let neg = encoder2.solver.not(term2);
    encoder2.assert_term(neg);
    let witness = eq(method_call(view(var("result")), "len", vec![]), int(1));
    let witness_term = encoder2
        .encode_pure(&witness)
        .expect("length-1 witness should encode");
    encoder2.assert_term(witness_term);
    let neg_new_result = encoder2.check_sat();
    assert!(
        matches!(neg_new_result, SolveResult::Sat),
        "NOT(result@.len() == 0) should be Sat, got {neg_new_result:?}"
    );
}

/// Test `Vec::get` contract with `index_logic`
///
/// Postcondition fragment: *r == `self@.index_logic(index`@)
#[test]
#[timeout(30000)]
fn test_vec_get_index_logic_encodes() {
    let mut encoder = AYEncoder::new();

    // self@.index_logic(i)
    let self_view = view(var("self"));
    let index_call = method_call(self_view, "index_logic", vec![var("i")]);

    // *r == self@.index_logic(i)
    let postcond = eq(deref(var("r")), index_call);

    let term = encoder
        .encode_pure(&postcond)
        .expect("Vec::get index_logic postcondition should encode");

    // Semantic: the encoded equality is satisfiable (verifies well-sorted Bool encoding).
    encoder.assert_term(term);
    let get_result = encoder.check_sat();
    assert!(
        matches!(get_result, SolveResult::Sat),
        "Vec::get index_logic postcondition should be Sat, got {get_result:?}"
    );

    // Verify postcondition is contingent: its negation should also be Sat.
    let mut encoder2 = AYEncoder::new();
    let postcond2 = eq(
        deref(var("r")),
        method_call(view(var("self")), "index_logic", vec![var("i")]),
    );
    let term2 = encoder2
        .encode_pure(&postcond2)
        .expect("postcond should re-encode");
    let neg = encoder2.solver.not(term2);
    encoder2.assert_term(neg);
    let neg_get_result = encoder2.check_sat();
    assert!(
            matches!(neg_get_result, SolveResult::Sat),
            "NOT(*r == self@.index_logic(i)) should be Sat — postcondition is contingent, got {neg_get_result:?}"
        );
}
