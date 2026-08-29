// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{sync::Arc, time::Duration};

use super::*;
mod ghost_seq_push_back;

/// Verify that closure capture projections fire when `c_final` is in the
/// encoder's variable set. This simulates the scenario where:
/// - A closure `c` captures mutable `x`
/// - The postcondition references `c_final` (closure post-state)
/// - The postcondition references `x_final` (captured variable post-state)
///
/// After capture projection, `capture_0(c_final) == x_final` should be
/// asserted, enabling the solver to connect closure struct accessors to
/// caller variables.
#[test]
#[timeout(60000)]
fn test_closure_capture_projection_via_verify_request() {
    use crate::{verify::VerificationRequest, CaptureKind};

    let closure_def_id = "test::test_fn::closure#0";
    let captures = vec![crate::closure_capture_info! {
        def_id: closure_def_id.to_string(),
        captures: vec![crate::CaptureField::new(
            "x",
            crate::ExprSort::Int,
            CaptureKind::ByRef,
        )],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    // Model: requires x == 100, ensures x_final == 101
    // Body: c_final represents closure post-state after c()
    //       x_final is the captured variable's post-state
    //
    // The capture projection should assert: capture_0(c_final) == x_final
    // Together with postcondition_mut saying capture_0(c_final) == x + 1,
    // this should give x_final == x + 1 == 101.
    //
    // For now, we just verify the integration path doesn't error and that
    // the closure struct sort gets registered (variables c_final and x_final
    // must appear in the contract expressions for the projection to fire).
    let req = eq(var("x"), int(100));
    // Use c_final and x_final in ensures so they exist in the encoder.
    let ens = eq(var("x_final"), int(101));
    let body = var("c_final");

    let reqs = [req];
    let enss = [ens];
    let request = VerificationRequest::new(&reqs, &enss)
        .return_expr(Some(&body))
        .closure_captures(Some(&captures));

    let result = verify_function_with_modes(request);
    assert!(
        result.is_ok(),
        "closure capture integration should not error: {result:?}"
    );
    // The verification should fail concretely without a postcondition_mut
    // fact connecting the closure post-state to x + 1. This keeps the
    // projection integration check from accepting solver incompleteness as
    // success.
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Failed(_)),
        "without postcondition_mut, x_final == 101 should fail (got: {vr:?})"
    );
}

/// Verify that conflicting capture signatures for the same closure def_id
/// are rejected through the `verify_function_with_modes` request path. (#1485)
#[test]
#[timeout(30000)]
fn test_verify_request_rejects_conflicting_closure_capture_signatures() {
    use crate::{verify::VerificationRequest, CaptureKind};

    let captures = vec![
        crate::closure_capture_info! {
            def_id: "test::closure#0".to_string(),
            captures: vec![crate::CaptureField::new(
                "x",
                crate::ExprSort::Int,
                CaptureKind::ByRef,
            )],
            param_name: Some("c".to_string()),
            body_expr: None,
            param_names: None,
            ensures_exprs: None,
        },
        crate::closure_capture_info! {
            def_id: "test::closure#0".to_string(),
            captures: vec![crate::CaptureField::new(
                "x",
                crate::ExprSort::Bool,
                CaptureKind::ByRef,
            )],
            param_name: Some("c".to_string()),
            body_expr: None,
            param_names: None,
            ensures_exprs: None,
        },
    ];

    let ensures = [eq(var("result"), int(0))];
    let request = VerificationRequest::new(&[], &ensures).closure_captures(Some(&captures));

    let result = verify_function_with_modes(request);
    assert!(
        result.is_err(),
        "conflicting closure capture signatures should return Err, got: {result:?}"
    );

    let msg = format!(
        "{}",
        result.expect_err("expected capture signature mismatch error")
    );
    assert!(
        msg.contains("changed capture signature"),
        "error should mention changed capture signature, got: {msg}"
    );
}

/// Test that a push_back chain produces verifiable length through a view.
///
/// This tests the #1317 Array+Length encoding: body returns a Seq-annotated
/// push_back chain `seq_empty().push_back(0).push_back(1)`, postcondition
/// checks `result@.len() == 2`. With SeqValue propagation and view identity,
/// the solver should prove this without quantifier instantiation.
#[test]
#[timeout(60000)]
fn test_seq_push_back_chain_len_via_view() {
    // Body: seq_empty().push_back(0).push_back(1) — Seq-annotated result
    let empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let push1 = method_call(empty, "push_back", vec![int(0)]);
    let push2 = method_call(push1, "push_back", vec![int(1)]);
    // Wrap in Var with Seq sort annotation to ensure result gets Seq sort
    // (mimics MIR extraction annotating return value as Seq).

    // Postcondition: result@.len() == 2
    let result_view_len = method_call(view(var("result")), "len", vec![]);
    let ens = eq(result_view_len, int(2));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&push2))
            .timeout(Some(Duration::from_secs(1))),
    );
    assert!(
        result.is_ok(),
        "Push-back chain verification should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "Push-back chain len via view should verify with Array encoding (#1317): {vr:?}",
    );
}

/// Test that a push_back chain element access verifies through a view.
///
/// Body: `seq_empty().push_back(42)`, postcondition: `result@[0] == 42`.
/// This tests the read-over-write-same property of the Array encoding.
#[test]
#[timeout(60000)]
fn test_seq_push_back_index_via_view() {
    let empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let push1 = method_call(empty, "push_back", vec![int(42)]);

    // Postcondition: result@[0] == 42
    let result_idx = method_call(view(var("result")), "index_logic", vec![int(0)]);
    let ens = eq(result_idx, int(42));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&push1))
            .timeout(Some(Duration::from_secs(1))),
    );
    assert!(
        result.is_ok(),
        "Push-back index verification should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "Push-back index via view should verify with Array encoding (#1317): {vr:?}",
    );
}

/// Ghost tuple mutation with post-state semantics from ghost/assert_in_ghost.rs.
///
/// Models `let mut p = (2, 3); p.0 = 4; proof_assert!(p.0 == 4); proof_assert!(p.1 == 3)`.
///
/// After the #2533 fix, the driver produces a post-state substitution where
/// the projected write has been applied to the initial tuple. The proof_assert
/// path sees `p == tuple2(4, 3)` (post-mutation), not the stale `tuple2(2, 3)`.
///
/// Verification succeeds non-vacuously:
/// - `tuple_get_0(tuple2(4, 3)) == 4` → `4 == 4` ✓
/// - `tuple_get_1(tuple2(4, 3)) == 3` → `3 == 3` ✓
///
/// Re: #2533, replaces previous contradictory-context model from #1572.
#[test]
#[timeout(60000)]
fn test_tuple_projected_write_proof_assert_ghost_mutate() {
    use trust_wp_core::formula::internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_name,
    };

    let tuple2_name = tuple_logic_fn_name(2);
    let get_0_name = tuple_field_logic_fn_name(0);
    let get_1_name = tuple_field_logic_fn_name(1);

    // Post-state substitution: p == tuple2(4, 3) (after p.0 = 4 applied)
    let req_post_state = eq(var("p"), logic_fn_call(&tuple2_name, vec![int(4), int(3)]));

    // Assertion 1: tuple_get_0(p) == 4 (mutated field)
    let assertion_field_0 = eq(logic_fn_call(&get_0_name, vec![var("p")]), int(4));
    // Assertion 2: tuple_get_1(p) == 3 (untouched field)
    let assertion_field_1 = eq(logic_fn_call(&get_1_name, vec![var("p")]), int(3));

    // Verify mutated field
    let result = verify_function_with_modes(VerificationRequest::new(
        &[req_post_state.clone()],
        &[assertion_field_0],
    ));
    assert!(
        result.is_ok(),
        "ghost_mutate post-state encoding should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "ghost_mutate tuple_get_0(p)==4 should verify non-vacuously with post-state (#2533): {vr:?}"
    );

    // Verify untouched field
    let result = verify_function_with_modes(VerificationRequest::new(
        &[req_post_state],
        &[assertion_field_1],
    ));
    assert!(
        result.is_ok(),
        "ghost_mutate post-state untouched field should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "ghost_mutate tuple_get_1(p)==3 should verify with post-state (#2533): {vr:?}"
    );
}

/// Ghost tuple mutation with symbolic projected-write facts.
///
/// Models the intermediate state where the driver preserves symbolic identity
/// for the projected write: `tuple_get_0(carrier) == 4` stays symbolic instead
/// of collapsing to `(2 == 4)`. The carrier plus the projected write fact
/// together imply the mutated field value.
///
/// Re: #2533, #994.
#[test]
#[timeout(30000)]
fn test_tuple_projected_write_proof_assert_ghost_mutate_symbolic_carrier() {
    use trust_wp_core::formula::internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_name,
    };

    let tuple2_name = tuple_logic_fn_name(2);
    let get_0_name = tuple_field_logic_fn_name(0);

    // Symbolic carrier: call_7 is the deref_mut intermediate
    // Projected write fact: tuple_get_0(call_7) == 4 (symbolic, not collapsed)
    let req_projected_write = eq(logic_fn_call(&get_0_name, vec![var("call_7")]), int(4));
    // Post-state link: p is resolved from the carrier with the write applied
    let req_post_state = eq(var("p"), logic_fn_call(&tuple2_name, vec![int(4), int(3)]));

    // Assertion: tuple_get_0(p) == 4
    let assertion = eq(logic_fn_call(&get_0_name, vec![var("p")]), int(4));

    let result = verify_function_with_modes(VerificationRequest::new(
        &[req_projected_write, req_post_state],
        &[assertion],
    ));
    assert!(
        result.is_ok(),
        "symbolic carrier ghost_mutate should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "symbolic carrier ghost_mutate should verify via post-state (#2533): {vr:?}"
    );
}

/// Ghost FSet length chain: replicates the exact precondition scenario
/// from `ghost_set.rs` where `proof_assert!(set.len() == 1)` fails.
///
/// The chain is:
/// 1. call_1.len() == 0                       (FSet::new postcondition)
/// 2. forall<x> !call_1.contains(x)           (FSet::new postcondition)
/// 3. call_8 == !call_1.contains(1)           (insert_ghost: result == !self.contains(arg1))
/// 4. ^call_1.contains(1)                     (insert_ghost: (^self).contains(arg1))
/// 5. call_8 ==> ^call_1.len() == call_1.len() + 1  (insert_ghost: fresh element)
/// 6. !call_8 ==> ^call_1.len() == call_1.len()     (insert_ghost: already present)
///
/// Goal: ^call_1.len() == 1
///
/// To verify, the solver must:
/// - Instantiate forall with x=1 to get !call_1.contains(1)
/// - Derive call_8 == true
/// - Fire the implication call_8 ==> ^call_1.len() == call_1.len() + 1
/// - Simplify 0 + 1 == 1
///
/// Part of #1581.
#[test]
#[timeout(30000)]
fn test_ghost_fset_length_chain_after_single_insert() {
    use crate::ExprSort;

    // Encode using method_call so fmap_len and fset_contains UFs are declared
    let call_1 = var("call_1");
    let final_call_1 = final_expr(var("call_1"));
    // call_8 is the bool return of insert_ghost (true if element was fresh)
    let call_8 = var_with_sort("call_8", ExprSort::Bool);

    // FSet::new postconditions
    let new_len_zero = eq(method_call(call_1.clone(), "len", vec![]), int(0));
    let new_forall_empty = forall(
        "x",
        not(method_call(call_1.clone(), "contains", vec![var("x")])),
    );

    // FSet::insert_ghost postconditions (inserting element 1)
    let insert_final_contains = method_call(final_call_1.clone(), "contains", vec![int(1)]);
    let insert_result_eq = eq(
        call_8.clone(),
        not(method_call(call_1.clone(), "contains", vec![int(1)])),
    );
    let insert_fresh_len = implies(
        call_8.clone(),
        eq(
            method_call(final_call_1.clone(), "len", vec![]),
            add(method_call(call_1.clone(), "len", vec![]), int(1)),
        ),
    );
    let insert_dup_len = implies(
        not(call_8.clone()),
        eq(
            method_call(final_call_1.clone(), "len", vec![]),
            method_call(call_1.clone(), "len", vec![]),
        ),
    );

    // All preconditions from the ghost context
    let preconditions = vec![
        new_len_zero,
        new_forall_empty,
        insert_final_contains,
        insert_result_eq,
        insert_fresh_len,
        insert_dup_len,
    ];

    // Goal: ^call_1.len() == 1
    let goal = eq(method_call(final_call_1.clone(), "len", vec![]), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&preconditions)),
    );

    assert!(
        result.is_ok(),
        "ghost FSet length chain should not produce encoding error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "ghost FSet length chain should verify ^call_1.len()==1 after insert into empty set: {vr:?}",
    );
}

/// Simpler variant: tests that ay can instantiate a forall with a ground term
/// and chain through an implication. Isolates quantifier E-matching from the
/// full FSet encoding.
///
/// Assumptions:
/// - f(a) == 0
/// - forall<x> !g(a, x)
/// - b == !g(a, 1)
/// - b ==> f(^a) == f(a) + 1
///
/// Goal: f(^a) == 1
///
/// Part of #1581.
#[test]
#[timeout(30000)]
fn test_quantifier_instantiation_through_implication_chain() {
    use crate::ExprSort;

    // Use logic_fn_call to create uninterpreted functions
    let f_a = logic_fn_call("f", vec![var("a")]);
    let f_final_a = logic_fn_call("f", vec![var("final_a")]);
    let g_a_x = logic_fn_call("g", vec![var("a"), var("x")]);
    let g_a_1 = logic_fn_call("g", vec![var("a"), int(1)]);
    // b is boolean (result of a boolean expression)
    let b = var_with_sort("b", ExprSort::Bool);

    let preconditions = vec![
        // f(a) == 0
        eq(f_a.clone(), int(0)),
        // forall<x> !g(a, x)
        forall("x", not(g_a_x)),
        // b == !g(a, 1)
        eq(b.clone(), not(g_a_1)),
        // b ==> f(final_a) == f(a) + 1
        implies(b.clone(), eq(f_final_a.clone(), add(f_a.clone(), int(1)))),
    ];

    // Goal: f(final_a) == 1
    let goal = eq(f_final_a, int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&preconditions)),
    );

    assert!(
        result.is_ok(),
        "quantifier+implication chain should not produce encoding error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "quantifier+implication chain should verify f(^a)==1: {vr:?}",
    );
}

/// Ground version of the quantifier chain test (no forall). Validates that
/// the solver can handle the implication chain reasoning without quantifiers.
///
/// Assumptions (all ground):
/// - f(a) == 0
/// - !g(a, 1)            (manually instantiated from the forall)
/// - b == !g(a, 1)
/// - b ==> f(final_a) == f(a) + 1
///
/// Goal: f(final_a) == 1
///
/// Part of #1581.
#[test]
#[timeout(30000)]
fn test_ghost_ground_implication_chain() {
    use crate::ExprSort;

    let f_a = logic_fn_call("f", vec![var("a")]);
    let f_final_a = logic_fn_call("f", vec![var("final_a")]);
    let g_a_1 = logic_fn_call("g", vec![var("a"), int(1)]);
    let b = var_with_sort("b", ExprSort::Bool);

    let preconditions = vec![
        // f(a) == 0
        eq(f_a.clone(), int(0)),
        // !g(a, 1) — ground instantiation of forall<x> !g(a, x)
        not(g_a_1.clone()),
        // b == !g(a, 1)
        eq(b.clone(), not(g_a_1)),
        // b ==> f(final_a) == f(a) + 1
        implies(b.clone(), eq(f_final_a.clone(), add(f_a.clone(), int(1)))),
    ];

    // Goal: f(final_a) == 1
    let goal = eq(f_final_a, int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&preconditions)),
    );

    assert!(
        result.is_ok(),
        "ground implication chain should not produce encoding error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "ground implication chain should verify f(^a)==1: {vr:?}",
    );
}

/// Minimal test: b is true, b ==> x == 1, goal: x == 1.
/// Pure Bool+arithmetic with no UFs.
///
/// Part of #1581.
#[test]
#[timeout(30000)]
fn test_ghost_minimal_implication_chain() {
    use crate::ExprSort;

    let b = var_with_sort("b", ExprSort::Bool);
    let x = var("x");

    let preconditions = vec![
        // b is true
        b.clone(),
        // b ==> x == 1
        implies(b.clone(), eq(x.clone(), int(1))),
    ];

    let goal = eq(x, int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&preconditions)),
    );

    assert!(
        result.is_ok(),
        "minimal implication chain should not produce encoding error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "minimal implication chain should verify x==1: {vr:?}"
    );
}

/// Test with UF: f(a) == 0, b is true, b ==> f(b_var) == f(a) + 1.
/// Goal: f(b_var) == 1.
///
/// Part of #1581.
#[test]
#[timeout(30000)]
fn test_ghost_uf_implication_chain() {
    use crate::ExprSort;

    let f_a = logic_fn_call("f", vec![var("a")]);
    let f_b_var = logic_fn_call("f", vec![var("b_var")]);
    let b = var_with_sort("b", ExprSort::Bool);

    let preconditions = vec![
        // f(a) == 0
        eq(f_a.clone(), int(0)),
        // b is true
        b.clone(),
        // b ==> f(b_var) == f(a) + 1
        implies(b.clone(), eq(f_b_var.clone(), add(f_a.clone(), int(1)))),
    ];

    let goal = eq(f_b_var, int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&preconditions)),
    );

    assert!(
        result.is_ok(),
        "UF implication chain should not produce encoding error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "UF implication chain should verify f(b_var)==1: {vr:?}",
    );
}

/// Ghost FMap insert_ghost mutation: model ghost context providing
/// the effects of `insert_ghost(key, value)` on an empty FMap.
///
/// Ghost context facts:
/// - m.len() == 0                        (FMap::new postcondition)
/// - ^m.contains(1)                      (insert_ghost: ^self.contains(key))
/// - ^m.get(1) == Some(42)               (insert_ghost: ^self.get(key) == Some(value))
/// - ^m.len() == m.len() + 1             (insert_ghost: fresh key)
///
/// Goal: ^m.len() == 1
///
/// This validates AC4 for #1581: ghost-specific API specs (insert_ghost, len)
/// produce the correct SMT encoding via ghost context.
///
/// Part of #1581.
#[test]
#[timeout(30000)]
fn test_ghost_fmap_insert_ghost_len() {
    let m = var("m");
    let final_m = final_expr(var("m"));

    let ghost_facts = vec![
        // m.len() == 0 (FMap::new)
        eq(method_call(m.clone(), "len", vec![]), int(0)),
        // ^m.contains(1) == true (insert_ghost postcondition)
        method_call(final_m.clone(), "contains", vec![int(1)]),
        // ^m.len() == m.len() + 1 (fresh key insertion)
        eq(
            method_call(final_m.clone(), "len", vec![]),
            add(method_call(m.clone(), "len", vec![]), int(1)),
        ),
    ];

    // Goal: ^m.len() == 1
    let goal = eq(method_call(final_m, "len", vec![]), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&ghost_facts)),
    );

    assert!(
        result.is_ok(),
        "ghost FMap insert_ghost len should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "ghost FMap insert_ghost on empty map should verify ^m.len()==1: {vr:?}",
    );
}

/// Ghost mutation with body result: ghost context constrains a variable
/// that the function body returns.
///
/// Models: `ghost! { let g = Ghost::new(seq_empty().push_back(x)); }`
/// where `x == 7`, body returns `g.len()`, postcondition says `result == 1`.
///
/// Part of #1581.
#[test]
#[timeout(60000)]
fn test_ghost_mutation_feeds_return_expr() {
    let empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };

    let ghost_facts = vec![
        eq(var("x"), int(7)),
        eq(var("g"), method_call(empty, "push_back", vec![var("x")])),
    ];

    // Body returns g.len() (via view)
    let body = method_call(view(var("g")), "len", vec![]);
    // Postcondition: result == 1
    let goal = eq(var("result"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&ghost_facts))
            .return_expr(Some(&body))
            .timeout(Some(Duration::from_secs(1))),
    );
    assert!(
        result.is_ok(),
        "ghost mutation feeding body result should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "ghost Seq mutation feeding body result should verify result==1: {vr:?}",
    );
}

/// Regression test for #1927: ghost context formulas get formula sort hints
/// while return_expr (a value expression) does NOT get formula sort hints.
///
/// Before the fix, `register_formula_sort_hints` was applied to all
/// `context_exprs` including `return_expr`, causing body-result variables
/// like `x` to be marked as Bool-sorted. When `x` is then used in
/// arithmetic postconditions (e.g., `result == x + 1`), ay panics with
/// "sort mismatch: got Bool, expected Int".
///
/// This test models: body returns `x`, ghost context asserts `x > 0`
/// (a formula that correctly marks `x` as having formula context),
/// and postcondition checks `result > 0` (arithmetic on `result`).
/// Without the #1927 fix, `x` would be marked Bool from return_expr's
/// formula_sort_hints pass, causing the `result > 0` check to fail
/// with a sort mismatch panic.
///
/// Part of #1581, Re: #1927.
#[test]
#[timeout(60000)]
fn test_ghost_context_formula_sort_hints_no_return_expr_contamination() {
    let ghost_facts = vec![
        // Ghost context: x > 0 (formula — leaf var `x` IS in formula context)
        PureExpr::BinOp(
            Arc::new(var("x")),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(int(0)),
        ),
    ];

    // Body returns x (value expression — leaf var `x` should NOT be Bool-marked)
    let body = var("x");

    // Postcondition: result > 0 (arithmetic comparison on result)
    let goal = PureExpr::BinOp(
        Arc::new(var("result")),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(int(0)),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&ghost_facts))
            .return_expr(Some(&body)),
    );

    assert!(
        result.is_ok(),
        "ghost context with return_expr should not cause sort mismatch (#1927): {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "ghost context x>0 with body=x should verify result>0: {vr:?}"
    );
}
