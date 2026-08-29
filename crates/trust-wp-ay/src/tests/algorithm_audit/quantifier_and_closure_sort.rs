// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quantifier and closure sort boundary tests (#1245, #1246, #1247, #1263).

use std::sync::Arc;

use ay_dpll::api::SolveResult;
use ntest::timeout;

use super::super::helpers::{and, logic_fn_call, match_expr, method_call, var};
use crate::{
    verify_function_with_modes, AYEncoder, ExprSort, Pattern, PureExpr, VerificationRequest,
    VerificationResult,
};

// --- flatten_nested_existentials trigger boundary (#1245) ---
//
// After fix: `flatten_nested_existentials` stops at triggered existentials,
// consistent with `collect_nested_quantifier_vars` in logic_fn.rs.
// E-matching handles triggered levels; eager instantiation handles triggerless.

/// Triggered outer exists with triggerless inner: outer triggers mean
/// E-matching handles the chain, eager instantiation is skipped entirely.
#[test]
#[timeout(30000)]
fn triggered_outer_exists_with_triggerless_inner_encodes() {
    // ensures: exists<a:Bool> {:pattern f(a)} exists<b:Bool> (a && b)
    let inner = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(and(var("a"), var("b"))),
        triggers: vec![],
    };
    let ensures = vec![PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(inner),
        triggers: vec![vec![logic_fn_call("f", vec![var("a")])]],
    }];

    let result = verify_function_with_modes(VerificationRequest::new(&[], &ensures));
    // Outer has triggers → flatten returns None → eager instantiation skipped.
    // E-matching + Bool expansion still finds the witness.
    let vr = result.expect("triggered nested exists should encode");
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "expected Verified for satisfiable nested exists, got {vr:?}"
    );
}

/// Triggerless outer with triggered inner: only outer variable collected
/// for eager instantiation; inner handled by E-matching.
#[test]
#[timeout(30000)]
fn triggerless_outer_exists_with_triggered_inner_encodes() {
    // ensures: exists<a:Bool> exists<b:Bool> {:pattern g(b)} (a && b)
    let inner = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(and(var("a"), var("b"))),
        triggers: vec![vec![logic_fn_call("g", vec![var("b")])]],
    };
    let ensures = vec![PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(inner),
        triggers: vec![],
    }];

    let result = verify_function_with_modes(VerificationRequest::new(&[], &ensures));
    // Only "a" collected for eager instantiation; "b" left for E-matching.
    let vr = result.expect("triggerless outer with triggered inner should encode");
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "expected Verified for satisfiable nested exists, got {vr:?}"
    );
}

// --- expr_mentions_bound_var match arm shadowing (#1246) ---
//
// The match arm shadowing bug affects resolve call collection in eager
// instantiation. This test exercises match arms that shadow existential
// bound variables.

/// Existential postcondition with match arm that shadows the bound variable.
/// `expr_mentions_bound_var` incorrectly reports the variable as mentioned
/// in the arm body (false positive), causing a ay sort panic during encoding.
///
/// BUG (#1246): The match arm `a => a` introduces a binding that shadows the
/// existential var `a`. Because `expr_mentions_bound_var` doesn't track
/// shadowing, eager instantiation resolves `a` with a Bool-sorted value in a
/// context where the match arm binding has Int sort.
///
/// Previously this triggered `BUG: mk_not expects Bool, got Int` in ay,
/// caught by `catch_ay_sort_panics` → `Unknown`. After the Bool coercion
/// safety net (`coerce_bool_operand`, fc3dc511), the sort mismatch is
/// handled gracefully at the encoding layer. The solver now finds a
/// counterexample rather than crashing — the shadowing bug still causes
/// incorrect semantics (#1246), but verification completes.
#[test]
#[timeout(30000)]
fn match_arm_rebinding_existential_var_encodes() {
    // ensures: exists<a:Bool> match x { a => a }
    // The "a" in the match arm is the pattern binding, not the existential var.
    let body = match_expr(
        var("x"),
        vec![(Pattern::Binding("a".to_string()), var("a"))],
    );
    let ensures = vec![PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(body),
        triggers: vec![],
    }];

    let result = verify_function_with_modes(VerificationRequest::new(&[], &ensures));
    // Bool coercion safety net (fc3dc511) prevents ay sort panic. The solver
    // now completes but finds a counterexample: the match-arm binding shadows
    // the existential var, producing incorrect semantics.
    // When #1246 is fixed, this should return Verified.
    match result {
        Ok(VerificationResult::Failed(_)) => {
            // Current path: Bool coercion prevents crash, solver finds counterexample.
        }
        Ok(VerificationResult::Unknown(ref reason))
            if reason.as_str().contains("ay solver panic") || reason.as_str().contains("sort") =>
        {
            // Legacy path: catch_unwind at verify layer caught the panic.
        }
        Err(ref e) if format!("{e:?}").contains("sort") => {
            // safe_apply path: encoder caught the panic as EncodingError.
        }
        other => {
            panic!(
                "BUG #1246: expected Failed (Bool coercion), Unknown(ay solver panic), \
                 or EncodingError for match-arm shadowing bug, got {other:?}"
            );
        }
    }
}

// --- substitute_vars_in_expr capture avoidance (#1247) ---
//
// The capture avoidance gap affects eager instantiation when substitution
// values contain free variables that collide with binder names.

/// Existential postcondition with let binding in body. If eager instantiation
/// substitutes a bound variable with a free variable name that matches the
/// let binding, the substitution incorrectly captures.
///
/// Despite the capture avoidance bug (#1247), this test currently produces
/// `Verified` because the Bool expansion instantiates a=true and a=false
/// directly, and the let-binding correctly evaluates in both cases.
#[test]
#[timeout(30000)]
fn let_binding_in_existential_body_encodes() {
    // ensures: exists<a:Bool> let x = a in x
    // Semantically: exists a in {true, false} such that (let x = a in x) = a.
    // Satisfiable by a = true.
    let body = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(var("a")),
        body: Arc::new(var("x")),
    };
    let ensures = vec![PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(body),
        triggers: vec![],
    }];

    let result = verify_function_with_modes(VerificationRequest::new(&[], &ensures));
    let vr = result.expect("let binding in existential body should encode");
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "expected Verified for satisfiable exists with let binding, got {vr:?}"
    );
}

// --- fn_mut_once witness sort alignment (#1263) ---
//
// The reverse fn_mut_once law should declare witness(self,args,result) with the
// same sort as the matched postcondition_mut res_state slot. Non-Bool/non-Int
// sorts still collapse to Int via closure_sort_from_tag("u") (#599).

/// Skolem witness function declared for a Bool-args closure uses Sort::Int
/// for the witness return type. This test documents the current behavior and
/// shows that the axiom fires correctly when all params are Int-sorted (the
/// common case). The axiom should maintain forward direction: postcondition_mut
/// implies postcondition_once.
#[test]
#[timeout(30000)]
fn skolem_witness_sort_int_forward_axiom_fires() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register postcondition_once (3-param: f, x, r) — all Int-sorted
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    // Register postcondition_mut (4-param: f, x, s, r) — all Int-sorted
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    encoder.assert_fn_mut_once_law();

    // Verify the Skolem witness function was created with Sort::Int
    let witness_key = "fn_mut_once_witness_3_i_i_i";
    assert!(
        encoder.decls().has_logic_func(witness_key),
        "Skolem witness function should be registered in logic_funcs"
    );

    // Forward direction: assert postcondition_mut AND NOT postcondition_once
    // Should be Unsat (mut implies once via the law)
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    let both = encoder.solver_mut().and(mut_term, neg_once);
    encoder.assert_term(both);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "forward direction: postcondition_mut must imply postcondition_once"
    );
}

/// Skolem witness function return sort is always Sort::Int. When the "u"
/// (uninterpreted) sort tag is used for non-Bool/non-Int parameters,
/// closure_sort_from_tag maps it to Sort::Int. This means the Skolem
/// function's return sort matches the axiom's variable sorts — but only
/// because ALL non-Bool sorts collapse to Int. This test verifies that the
/// witness symbol name encodes the collapsed sort tags, documenting the
/// current sort-collapsing behavior.
#[test]
#[timeout(30000)]
fn closure_sort_tag_collapses_non_bool_to_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register postcondition_once with 4 params to create a distinct signature.
    // All params are Int-sorted (no Bool), so sort tags are all "i".
    let once_expr = method_call(
        var("f"),
        "postcondition_once",
        vec![var("x"), var("y"), var("r")],
    );
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    // Register postcondition_mut with 5 params (extra res_state)
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("y"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    encoder.assert_fn_mut_once_law();

    // The witness function name should include "_i_i_i_i" (all Int tags)
    // because closure_sort_tag returns "i" for Sort::Int and "u" for others,
    // and closure_sort_from_tag("u") maps back to Sort::Int.
    let witness_key = "fn_mut_once_witness_4_i_i_i_i";
    assert!(
        encoder.decls().has_logic_func(witness_key),
        "4-param witness function should have all-Int sort tags: expected key '{witness_key}', \
         available keys: {:?}",
        encoder
            .decls()
            .logic_func_names()
            .filter(|k| k.contains("witness"))
            .collect::<Vec<_>>()
    );
}

/// Bool-sorted parameters produce "b" sort tags in the witness name.
/// This test verifies that Bool args are correctly distinguished from Int
/// in the Skolem function naming, which is important for multi-signature
/// coexistence (different closures with different sort signatures need
/// separate witness functions).
#[test]
#[timeout(30000)]
fn skolem_witness_bool_args_produce_distinct_tags() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // postcondition_once with Bool arg: (f, Bool, r) → sort tags: i_b_i
    let once_expr = method_call(
        var("f"),
        "postcondition_once",
        vec![PureExpr::Bool(true), var("r")],
    );
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once with Bool arg should encode");

    // postcondition_mut with Bool arg: (f, Bool, s, r) → sort tags: i_b_i_i
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![PureExpr::Bool(true), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut with Bool arg should encode");

    encoder.assert_fn_mut_once_law();

    // The witness function should have "b" in the sort signature for the Bool param
    let witness_key = "fn_mut_once_witness_3_i_b_i";
    assert!(
        encoder.decls().has_logic_func(witness_key),
        "Bool param should produce 'b' tag in witness name: expected '{witness_key}', \
         available keys: {:?}",
        encoder
            .decls()
            .logic_func_names()
            .filter(|k| k.contains("witness"))
            .collect::<Vec<_>>()
    );
}

/// Reverse fn_mut_once law should support Bool-typed res_state.
///
/// Regression for #1263: when the matched postcondition_mut signature has
/// Bool state (`closure_postcondition_mut_4_i_i_b_i`), the witness function
/// must return Bool so `postcondition_mut(f, x, witness(...), r)` is well-sorted.
#[test]
#[timeout(30000)]
fn skolem_witness_bool_res_state_reverse_axiom_fires() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // once: (f, x, r) -> Bool predicate (sort tags i_i_i)
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    // mut: (f, x, s:Bool, r) -> Bool predicate (sort tags i_i_b_i)
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), PureExpr::Bool(true), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut with Bool res_state should encode");

    encoder.assert_fn_mut_once_law();

    let once_decl = encoder
        .decls()
        .get_logic_func("closure_postcondition_once_3_i_i_i")
        .cloned()
        .expect("once declaration should exist");
    let mut_decl = encoder
        .decls()
        .get_logic_func("closure_postcondition_mut_4_i_i_b_i")
        .cloned()
        .expect("bool-state mut declaration should exist");
    let witness_decl = encoder
        .decls()
        .get_logic_func("fn_mut_once_witness_3_i_i_i_b")
        .cloned()
        .expect("bool-state witness function should be declared");

    let f = encoder
        .get_or_declare_var("f", ay_dpll::api::Sort::Int)
        .expect("declare f");
    let x = encoder
        .get_or_declare_var("x", ay_dpll::api::Sort::Int)
        .expect("declare x");
    let r = encoder
        .get_or_declare_var("r", ay_dpll::api::Sort::Int)
        .expect("declare r");

    let once_term = encoder.solver.apply(&once_decl, &[f, x, r]);
    let witness_term = encoder.solver.apply(&witness_decl, &[f, x, r]);
    let mut_term = encoder.solver.apply(&mut_decl, &[f, x, witness_term, r]);

    // Reverse law: once(f,x,r) implies mut(f,x,witness(f,x,r),r)
    encoder.assert_term(once_term);
    let not_mut_term = encoder.solver.not(mut_term);
    encoder.assert_term(not_mut_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "reverse law should force bool-state postcondition_mut at witness"
    );
}

/// Eager fn_mut_once instantiation should use the Bool-state witness symbol.
///
/// This validates the non-Int res_state lookup path in
/// assert_eager_fn_mut_once_instantiations (#1263).
#[test]
#[timeout(30000)]
fn eager_fn_mut_once_instantiation_supports_bool_res_state_witness() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), PureExpr::Bool(false), var("r")],
    );
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut with Bool res_state should encode");
    encoder.assert_fn_mut_once_law();
    encoder
        .assert_eager_fn_mut_once_instantiations(std::slice::from_ref(&once_expr))
        .expect("eager fn_mut_once instantiation should succeed");

    let mut_decl = encoder
        .decls()
        .get_logic_func("closure_postcondition_mut_4_i_i_b_i")
        .cloned()
        .expect("bool-state mut declaration should exist");
    let witness_decl = encoder
        .decls()
        .get_logic_func("fn_mut_once_witness_3_i_i_i_b")
        .cloned()
        .expect("bool-state witness function should be declared");

    let f = encoder
        .get_or_declare_var("f", ay_dpll::api::Sort::Int)
        .expect("declare f");
    let x = encoder
        .get_or_declare_var("x", ay_dpll::api::Sort::Int)
        .expect("declare x");
    let r = encoder
        .get_or_declare_var("r", ay_dpll::api::Sort::Int)
        .expect("declare r");
    let witness_term = encoder.solver.apply(&witness_decl, &[f, x, r]);
    let mut_term = encoder.solver.apply(&mut_decl, &[f, x, witness_term, r]);

    // Eager instantiation should have asserted this exact mut term.
    let not_mut_term = encoder.solver.not(mut_term);
    encoder.assert_term(not_mut_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "eager instantiation should assert bool-state mut postcondition at witness"
    );
}
