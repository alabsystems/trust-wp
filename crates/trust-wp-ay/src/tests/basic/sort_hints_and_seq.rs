// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
/// Cross-expression Bool sort registration via the unified sort-hint API.
///
/// `b == b` alone does not force Bool operands. If encoded first, `b` would be
/// declared as Int and later `!b` would fail. Pre-registering both expressions
/// ensures deterministic declaration order across separate encode calls.
#[test]
#[timeout(30000)]
fn test_register_sort_hints_bool_cross_expression() {
    let mut encoder = AYEncoder::new_pure();

    let requires_expr = eq(var("b"), var("b"));
    let ensures_expr = not(var("b"));

    encoder.register_sort_hints(&[requires_expr.clone(), ensures_expr.clone()]);

    let requires_term = encoder.encode_pure(&requires_expr);
    assert!(
        requires_term.is_ok(),
        "requires encoding should succeed with pre-registered hints: {requires_term:?}"
    );

    let ensures_term = encoder.encode_pure(&ensures_expr);
    assert!(
        ensures_term.is_ok(),
        "ensures encoding should succeed with pre-registered hints: {ensures_term:?}"
    );

    // Semantic: b == b is a tautology; its negation should be UNSAT
    let req = requires_term.unwrap();
    let neg_req = encoder.solver_mut().not(req);
    encoder.assert_term(neg_req);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(b == b) should be UNSAT (tautology)"
    );
}

/// Regression: Bool propagation through Ite branches (#544).
///
/// `Not(Ite(cond, Var("x"), Var("y")))` — the Ite result is in Bool context
/// (operand of Not), so both branch variables `x` and `y` must be declared as Bool.
/// Before the fix, `collect_names_as_bool` did not recurse into Ite branches.
#[test]
#[timeout(30000)]
fn test_register_sort_hints_bool_through_ite_branches() {
    let mut encoder = AYEncoder::new_pure();

    // Not(Ite(true, Var("x"), Var("y"))) — x and y should be Bool
    let expr = not(ite(bool_expr(true), var("x"), var("y")));
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    assert!(
        encoder.is_bool_var("x"),
        "x should be Bool (Ite then-branch in Not context)"
    );
    assert!(
        encoder.is_bool_var("y"),
        "y should be Bool (Ite else-branch in Not context)"
    );

    let term = encoder.encode_pure(&expr);
    assert!(
        term.is_ok(),
        "Not(Ite(true, x, y)) should encode without sort panic: {term:?}"
    );

    // Semantic: Not(Ite(true, x, y)) simplifies to Not(x). Assert it and check SAT.
    let t = term.unwrap();
    encoder.assert_term(t);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Not(Ite(true, x, y)) should be SAT (x can be false)"
    );
}

/// Regression: Bool propagation through Match arms (#544).
///
/// `Not(Match { arms: [Var("a"), Var("b")] })` — the Match result is in Bool
/// context, so arm body variables must be declared as Bool.
#[test]
#[timeout(30000)]
fn test_register_sort_hints_bool_through_match_arms() {
    use trust_wp_core::formula::Pattern;

    let mut encoder = AYEncoder::new_pure();

    let match_e = match_expr(
        int(0),
        vec![
            (Pattern::Literal(int(0)), var("a")),
            (Pattern::Wildcard, var("b")),
        ],
    );
    let expr = not(match_e);
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    assert!(
        encoder.is_bool_var("a"),
        "a should be Bool (Match arm body in Not context)"
    );
    assert!(
        encoder.is_bool_var("b"),
        "b should be Bool (Match arm body in Not context)"
    );

    let term = encoder.encode_pure(&expr);
    assert!(
        term.is_ok(),
        "Not(Match {{ ... }}) should encode without sort panic: {term:?}"
    );

    // Semantic: assert the encoded Not(Match{...}) and check SAT
    let t = term.unwrap();
    encoder.assert_term(t);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Not(Match with Bool arms) should be SAT"
    );
}

/// Regression: Not(LogicFnCall{name: "pred", args: []}) should encode without panic (#544).
///
/// Logic functions returning Bool appeared as Int-sorted placeholders when the function
/// was not yet registered. The pre-scan now records Bool sort hints for logic function
/// names used in Not/And/Or/Implies/Ite-condition contexts.
#[test]
#[timeout(30000)]
fn test_encode_not_logic_fn_call_bool_sort() {
    let mut encoder = AYEncoder::new();

    // Not(logic_fn("pred", [])) — pred should get Bool return sort
    let expr = not(logic_fn_call("pred", vec![]));
    let term = encoder.encode_pure(&expr);
    assert!(
        term.is_ok(),
        "Not(LogicFnCall) should encode without sort panic: {term:?}"
    );

    // Semantic: Not(pred()) should be SAT (pred can be false)
    let t = term.unwrap();
    encoder.assert_term(t);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Not(pred()) should be SAT (uninterpreted pred can be false)"
    );
}

/// Regression: And(LogicFnCall{..}, Bool(true)) should encode without panic (#544).
///
/// Logic function calls in And operand position need Bool return sort.
/// Verify both the sort hint mechanism and the encoding success.
#[test]
#[timeout(30000)]
fn test_encode_and_logic_fn_call_bool_sort() {
    let mut encoder = AYEncoder::new();

    // And(logic_fn("is_valid", [var("x")]), Bool(true))
    let expr = and(logic_fn_call("is_valid", vec![var("x")]), bool_expr(true));
    let term = encoder.encode_pure(&expr);
    assert!(
        term.is_ok(),
        "And(LogicFnCall, Bool) should encode without sort panic: {term:?}"
    );
    // Verify the sort hint mechanism identified the logic function as Bool-returning.
    // "is_valid" becomes "logic_is__valid" in SMT naming convention (#1435 injective encoding).
    assert!(
        encoder.is_bool_var("logic_is__valid"),
        "is_valid should be marked Bool after appearing in And operand position"
    );

    // Semantic: And(is_valid(x), true) simplifies to is_valid(x); assert it and check SAT
    let t = term.unwrap();
    encoder.assert_term(t);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "And(is_valid(x), true) should be SAT (uninterpreted is_valid can be true)"
    );
}

/// Regression: Eq(LogicFnCall{..}, Bool(true)) should encode without panic (#544).
///
/// When one side of Eq is Bool(true), the other side (a logic function call)
/// must also produce Bool. The pre-scan propagates Bool context through Eq.
#[test]
#[timeout(30000)]
fn test_encode_eq_logic_fn_call_with_bool() {
    let mut encoder = AYEncoder::new();

    // Eq(logic_fn("check", []), Bool(true)) — check should get Bool return sort
    let expr = eq(logic_fn_call("check", vec![]), bool_expr(true));
    let term = encoder.encode_pure(&expr);
    assert!(
        term.is_ok(),
        "Eq(LogicFnCall, Bool) should encode without sort panic: {term:?}"
    );

    // Semantic: check() == true is SAT (check can be true)
    let t = term.unwrap();
    encoder.assert_term(t);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Eq(check(), true) should be SAT (uninterpreted check can be true)"
    );
}

/// Regression: Not(LogicFnCall) with arguments should also work (#544).
///
/// Verifies that the fix works for parameterized logic functions like
/// `reflexive(result)` from `specification/logic_call.rs`.
#[test]
#[timeout(30000)]
fn test_encode_not_logic_fn_call_with_args() {
    let mut encoder = AYEncoder::new();

    // Not(logic_fn("reflexive", [var("result")])) — reflexive returns Bool
    let expr = not(logic_fn_call("reflexive", vec![var("result")]));
    let term = encoder.encode_pure(&expr);
    assert!(
        term.is_ok(),
        "Not(LogicFnCall with args) should encode without sort panic: {term:?}"
    );

    // Semantic: Not(reflexive(result)) should be SAT (reflexive can be false)
    let t = term.unwrap();
    encoder.assert_term(t);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Not(reflexive(result)) should be SAT"
    );
}

/// Regression: bare `LogicFnCall` postcondition negated at term level (#544).
///
/// Postconditions like `#[ensures(omg(x))]` are encoded as `encode_pure(omg(x))`
/// then negated with `solver.not(term)`. The pre-scan doesn't see the Not context.
/// `register_formula_sort_hints` marks top-level logic function calls as Bool.
#[test]
#[timeout(30000)]
fn test_postcondition_logic_fn_call_negation() {
    let mut encoder = AYEncoder::new();

    // Simulate the verify.rs pattern: encode postcondition, then negate
    let ensures_expr = logic_fn_call("omg", vec![var("x")]);
    encoder.register_sort_hints(std::slice::from_ref(&ensures_expr));
    encoder.register_formula_sort_hints(std::slice::from_ref(&ensures_expr));

    let post_term = encoder.encode_pure(&ensures_expr).unwrap();
    // This would panic with "BUG: mk_not expects Bool, got Int" before the fix.
    // The not() call validates Bool sort; assert the result is usable.
    let negated = encoder.solver_mut().not(post_term);
    encoder.solver_mut().assert_term(negated);
    let sat = encoder.solver_mut().check_sat().into_inner();
    // omg(x) is uninterpreted Bool, so its negation is SAT (model: omg(x) = false)
    assert!(
        matches!(sat, SolveResult::Sat),
        "negated uninterpreted Bool postcondition should be SAT, got {sat:?}"
    );
}

/// Regression: `seq![...]` macro calls should be Seq-sorted, not Int (#544).
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_seq_logic_fn_call() {
    use crate::encoder::infer_expr_sort;

    let seq_lit = logic_fn_call("seq", vec![int(0), int(1)]);
    assert_eq!(
        infer_expr_sort(&seq_lit),
        Sort::seq(Sort::Int),
        "seq![...] LogicFnCall should infer as Seq sort, not Int (#544)"
    );
}

/// Regression: `a@ == seq![...]` should encode without Seq/Int sort panic (#544).
#[test]
#[timeout(30000)]
fn test_encode_eq_view_seq_logic_fn_call() {
    let mut encoder = AYEncoder::new();

    let expr = eq(
        view(var("a")),
        logic_fn_call("seq", vec![int(0), int(1), int(1), int(0)]),
    );
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    let term = encoder.encode_pure(&expr);
    assert!(
        term.is_ok(),
        "Eq(View(_), LogicFnCall(seq)) should encode without sort panic: {term:?}"
    );

    // Semantic: verify the encoded term is Bool-sorted by successfully negating it.
    // The `not()` call validates that the term has Bool sort (would panic on non-Bool).
    let t = term.unwrap();
    let neg = encoder.solver_mut().not(t);
    encoder.solver_mut().assert_term(neg);
    let sat = encoder.solver_mut().check_sat().into_inner();
    assert!(
        matches!(sat, SolveResult::Sat),
        "negated Eq(View, Seq) should be Sat, got {sat:?}"
    );
}
