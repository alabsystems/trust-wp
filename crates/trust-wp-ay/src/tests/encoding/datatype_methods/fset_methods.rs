// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_fset_contains_declares_membership_uf() {
    let mut encoder = AYEncoder::new();

    let contains_expr = method_call(var("s"), "contains", vec![int(7)]);

    let term = encoder
        .encode_pure(&contains_expr)
        .expect("FSet.contains should encode");
    assert!(
        encoder.decls().has_spec_func("fset_contains"),
        "FSet.contains should declare membership UF"
    );

    // Semantic: contains(s, 7) is Bool-sorted and satisfiable (both true and false
    // assignments exist for uninterpreted predicates). Verifies sort correctness.
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "FSet.contains(s, 7) should be SAT, got {result:?}"
    );
}
#[test]
#[timeout(30000)]
fn test_fset_is_empty_declares_uf() {
    let mut encoder = AYEncoder::new();

    let is_empty_expr = method_call(var("s"), "is_empty", vec![]);

    let term = encoder
        .encode_pure(&is_empty_expr)
        .expect("FSet.is_empty should encode");
    assert!(
        encoder.decls().has_spec_func("fset_is_empty"),
        "FSet.is_empty should declare emptiness UF"
    );

    // Semantic: is_empty(s) is Bool-sorted and satisfiable
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "FSet.is_empty(s) should be SAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_fset_peek_declares_uf() {
    let mut encoder = AYEncoder::new();

    let peek_expr = method_call(var("s"), "peek", vec![]);

    let _term = encoder
        .encode_pure(&peek_expr)
        .expect("FSet.peek should encode");
    assert!(
        encoder.decls().has_spec_func("fset_peek"),
        "FSet.peek should declare element-return UF"
    );

    // Semantic: peek(s) returns Int, check it's usable in a constraint
    let zero = PureExpr::Int(0);
    let eq_expr = PureExpr::BinOp(
        Arc::new(method_call(var("s"), "peek", vec![])),
        BinOp::Eq,
        Arc::new(zero),
    );
    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("peek == 0 should encode");
    encoder.assert_term(eq_term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "FSet.peek(s) == 0 should be SAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_fset_remove_declares_uf() {
    let mut encoder = AYEncoder::new();

    let remove_expr = method_call(var("s"), "remove", vec![int(5)]);

    let _term = encoder
        .encode_pure(&remove_expr)
        .expect("FSet.remove should encode");
    assert!(
        encoder.decls().has_spec_func("fset_remove"),
        "FSet.remove should declare removal UF"
    );

    // Semantic: remove(s, 5) returns an Int (representing new FSet)
    let zero = PureExpr::Int(0);
    let neq_expr = PureExpr::BinOp(Arc::new(remove_expr), BinOp::Ne, Arc::new(zero));
    let neq_term = encoder
        .encode_pure(&neq_expr)
        .expect("remove != 0 should encode");
    encoder.assert_term(neq_term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "FSet.remove(s, 5) != 0 should be SAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_fset_intersection_declares_uf() {
    let mut encoder = AYEncoder::new();

    let intersection_expr = method_call(var("s"), "intersection", vec![var("t")]);

    let _term = encoder
        .encode_pure(&intersection_expr)
        .expect("FSet.intersection should encode");
    assert!(
        encoder.decls().has_spec_func("fset_intersection"),
        "FSet.intersection should declare set-intersection UF"
    );

    // Semantic: intersection(s, t) returns Int (representing a new FSet)
    let zero = PureExpr::Int(0);
    let neq_expr = PureExpr::BinOp(Arc::new(intersection_expr), BinOp::Ne, Arc::new(zero));
    let neq_term = encoder
        .encode_pure(&neq_expr)
        .expect("intersection != 0 should encode");
    encoder.assert_term(neq_term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "FSet.intersection(s, t) != 0 should be SAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_fset_difference_declares_uf() {
    let mut encoder = AYEncoder::new();

    let difference_expr = method_call(var("s"), "difference", vec![var("t")]);

    let _term = encoder
        .encode_pure(&difference_expr)
        .expect("FSet.difference should encode");
    assert!(
        encoder.decls().has_spec_func("fset_difference"),
        "FSet.difference should declare set-difference UF"
    );

    // Semantic: difference(s, t) returns Int (representing a new FSet)
    let zero = PureExpr::Int(0);
    let neq_expr = PureExpr::BinOp(Arc::new(difference_expr), BinOp::Ne, Arc::new(zero));
    let neq_term = encoder
        .encode_pure(&neq_expr)
        .expect("difference != 0 should encode");
    encoder.assert_term(neq_term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "FSet.difference(s, t) != 0 should be SAT, got {result:?}"
    );
}
/// Reproduction test for bug/vcgen: verify_function_with_modes with
/// is_empty in requires should not produce "unknown method call" error.
/// This mimics the logic function postcondition verification path (#893)
/// where the requires clause contains !s.is_empty().
#[test]
#[timeout(30000)]
fn test_fset_is_empty_in_verify_function_requires() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // Build a minimal logic function:
    //   fn set_peek(s: FSet<Int>) -> Int { s.peek() }
    //   requires: !s.is_empty()
    //   ensures: s.contains(result)
    let mut logic_fn = LogicFnDef::new(
        "set_peek".to_string(),
        "crate::set_peek".to_string(),
        vec!["s".to_string()],
        method_call(var("s"), "peek", vec![]),
    )
    .with_mode(LogicMode::Open);

    // requires: !s.is_empty()
    logic_fn.set_requires(vec![PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(method_call(var("s"), "is_empty", vec![])),
    )]);

    // ensures: s.contains(result)
    logic_fn.set_ensures(vec![method_call(var("s"), "contains", vec![var("result")])]);

    // Verify: this should NOT fail with "unknown method call: is_empty"
    let result = verify_function_with_modes(
        VerificationRequest::new(logic_fn.requires(), logic_fn.ensures())
            .return_expr(Some(logic_fn.body())),
    );

    // We don't need Verified — we just need no encoding error
    assert!(
        result.is_ok(),
        "is_empty in requires should not cause encoding error: {result:?}"
    );
}

/// Verify that the peek-contains FSet axiom is asserted: when the set is
/// non-empty, `s.contains(s.peek())` holds. This requires the demand guard
/// (#2674) to detect FSet usage and assert FSet axioms. Without the axioms,
/// the solver cannot link peek/contains and the postcondition fails.
///
/// Regression test for bug/vcgen (Part of #2694).
#[test]
#[timeout(30000)]
fn test_fset_peek_contains_axiom_verified_no_logic_fns() {
    // Verify: requires(!s.is_empty()) ==> ensures(s.contains(result))
    // where the body is s.peek().
    //
    // This should verify because:
    // 1. requires: !is_empty(s)
    // 2. body = result = peek(s)
    // 3. FSet axiom: !is_empty(s) ==> contains(s, peek(s))
    // 4. ensures: contains(s, result) = contains(s, peek(s)) = true
    let requires = vec![PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(method_call(var("s"), "is_empty", vec![])),
    )];
    let ensures = vec![method_call(var("s"), "contains", vec![var("result")])];
    let body = method_call(var("s"), "peek", vec![]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    );

    match &result {
        Ok(VerificationResult::Verified(_)) => {} // expected
        Ok(VerificationResult::Failed(_)) => {
            panic!(
                "peek-contains axiom should be verified but FAILED — \
                 FSet axioms may not be asserted (demand guard regression #2694)"
            );
        }
        other => {
            // Unknown/encoding error — also problematic but less specific
            panic!("peek-contains axiom verification unexpected result: {other:?}");
        }
    }
}

/// Same as the no_logic_fns variant, but with set_max registered as a
/// logic function — mimicking the driver's logic function postcondition
/// verification path where FSet methods may be intercepted by
/// try_logic_fn_dispatch.
///
/// Previously failed due to FSet/Seq sort misclassification: when logic
/// functions used FSet parameters with shared methods like `contains`,
/// the parameter was misclassified as Seq. Fixed by excluding parameters
/// used with FSet-only methods (peek, remove, is_empty, etc.) from the
/// Seq inference set. (#2701, bug/vcgen.rs regression)
///
/// Regression test for bug/vcgen sort misclassification (Part of #2694).
#[test]
#[timeout(30000)]
fn test_fset_peek_contains_axiom_sort_misclassification_with_logic_fns() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // Build set_max logic function (same structure as vcgen test).
    let inner_ite = ite(
        PureExpr::BinOp(Arc::new(var("x")), BinOp::Ge, Arc::new(var("rec"))),
        var("x"),
        var("rec"),
    );
    let rec_let = PureExpr::Let {
        var: "rec".to_string(),
        value: Arc::new(PureExpr::LogicFnCall {
            name: "set_max".to_string(),
            args: vec![var("s")],
        }),
        body: Arc::new(inner_ite),
    };
    let outer_ite = ite(method_call(var("s"), "is_empty", vec![]), var("x"), rec_let);
    let inner_let = PureExpr::Let {
        var: "s".to_string(),
        value: Arc::new(method_call(var("s"), "remove", vec![var("x")])),
        body: Arc::new(outer_ite),
    };
    let set_max_body = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(method_call(var("s"), "peek", vec![])),
        body: Arc::new(inner_let),
    };

    let mut set_max_fn = LogicFnDef::new(
        "set_max".to_string(),
        "crate::set_max".to_string(),
        vec!["s".to_string()],
        set_max_body,
    )
    .with_mode(LogicMode::Open);

    set_max_fn.set_requires(vec![PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(method_call(var("s"), "is_empty", vec![])),
    )]);
    set_max_fn.set_ensures(vec![method_call(var("s"), "contains", vec![var("result")])]);

    // Now verify the SIMPLE peek-contains with set_max as an available logic fn.
    let logic_fns = vec![set_max_fn];

    let requires = vec![PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(method_call(var("s"), "is_empty", vec![])),
    )];
    let ensures = vec![method_call(var("s"), "contains", vec![var("result")])];
    let body = method_call(var("s"), "peek", vec![]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(&logic_fns)),
    );

    // Fixed (#2701): FSet-only method exclusion in infer_seq_like_params
    // prevents misclassification of FSet parameters as Seq. The `s` parameter
    // uses `peek`, `remove`, and `is_empty` — all FSet-only methods — so it
    // is correctly excluded from Seq inference.
    match &result {
        Ok(VerificationResult::Verified(_)) => {} // expected
        other => {
            panic!(
                "peek-contains with logic_fns should now VERIFY after FSet/Seq sort \
                 disambiguation fix (#2701), got: {other:?}"
            );
        }
    }
}
