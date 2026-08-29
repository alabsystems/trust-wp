// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// =============================================================================
// fn_mut_once law tests (Phase 4, Part of #358)
//
// The fn_mut_once law connects FnMut to FnOnce:
//   postcondition_once(self, args, result) <==>
//     exists res_state. postcondition_mut(self, args, res_state, result)
//                       && resolve(res_state)
// =============================================================================

/// Test that the `fn_mut_once` law axiom is asserted when both `postcondition_once`
/// and `postcondition_mut` UF symbols are declared.
///
/// Scenario: encode both `postcondition_once` and `postcondition_mut` method calls,
/// then call `assert_fn_mut_once_law`. The law should create a biconditional
/// connecting them, making `postcondition_once` derivable from `postcondition_mut`.
#[test]
#[timeout(30000)]
fn test_fn_mut_once_law_asserted() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare postcondition_once(f, x, result) — three-place (self, arg, result)
    let once_call = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once symbol");

    // Declare postcondition_mut(f, x, ^f, result) — four-place
    let mut_call = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("r")],
    );
    encoder
        .encode_pure(&mut_call)
        .expect("declare postcondition_mut symbol");

    // Both symbols should be declared
    let once_count = encoder
        .decls()
        .logic_func_names()
        .filter(|k| k.starts_with("closure_postcondition_once_"))
        .count();
    let mut_count = encoder
        .decls()
        .logic_func_names()
        .filter(|k| k.starts_with("closure_postcondition_mut_"))
        .count();
    assert_eq!(once_count, 1, "Expected one postcondition_once symbol");
    assert_eq!(mut_count, 1, "Expected one postcondition_mut symbol");

    // Assert the law — should not panic and should not introduce contradictions
    encoder.assert_fn_mut_once_law();

    // Forward direction: postcondition_mut ==> postcondition_once
    // If the law axiom is asserted, assuming postcondition_mut and negating
    // postcondition_once should be UNSAT.
    let once_call_check = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let once_term = encoder
        .encode_pure(&once_call_check)
        .expect("encode postcondition_once for forward check");
    let mut_call_check = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("r")],
    );
    let mut_term = encoder
        .encode_pure(&mut_call_check)
        .expect("encode postcondition_mut for forward check");
    // Assume postcondition_mut holds, negate postcondition_once
    encoder.assert_term(mut_term);
    let neg_once = encoder.solver.not(once_term);
    encoder.assert_term(neg_once);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fn_mut_once law forward direction: mut ==> once should hold: {result:?}"
    );
}

/// Regression test for mixed-sort closure specs.
///
/// The `fn_mut_once` law must quantify with the actual signature sorts.
/// A Bool argument used to panic when all law variables were Int-sorted.
#[test]
#[timeout(30000)]
fn test_fn_mut_once_law_handles_bool_args() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let once_call = method_call(
        var("f"),
        "postcondition_once",
        vec![bool_expr(true), var("r")],
    );
    let once_term = encoder
        .encode_pure(&once_call)
        .expect("encode postcondition_once with Bool arg");

    let mut_call = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![bool_expr(true), var("s"), var("r")],
    );
    let mut_term = encoder
        .encode_pure(&mut_call)
        .expect("encode postcondition_mut with Bool arg");

    encoder.assert_fn_mut_once_law();
    assert!(
        encoder
            .decls()
            .has_logic_func("fn_mut_once_witness_3_i_b_i"),
        "Expected witness keyed by sort signature for Bool argument"
    );

    // Forward direction should still hold with Bool argument sorts:
    // postcondition_mut(f, true, s, r) ==> postcondition_once(f, true, r)
    encoder.assert_term(mut_term);
    let neg_once = encoder.solver.not(once_term);
    encoder.assert_term(neg_once);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fn_mut_once forward axiom should handle Bool args without sort mismatch: {result:?}"
    );
}

/// Test that the `fn_mut_once` law is a no-op when only `postcondition_once`
/// is declared (no matching `postcondition_mut`).
#[test]
#[timeout(30000)]
fn test_fn_mut_once_law_noop_without_mut() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Only declare postcondition_once
    let once_call = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once for noop test");

    // Should be a no-op (no matching mut symbol)
    encoder.assert_fn_mut_once_law();

    // Solver should still be satisfiable (no contradictions introduced)
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Should be SAT when law is no-op: {result:?}"
    );
}

/// Test the weakening chain: `postcondition_mut` implies `postcondition_once`.
///
/// Given:
///   - `postcondition_mut(f, x, f', result)` holds (from `FnMut::call_mut`)
/// Prove:
///   - `postcondition_once(f, x, result)` holds (via `fn_mut_once` law)
///
/// This is the core `FnMut` -> `FnOnce` weakening that enables calling
/// `FnMut` closures through `FnOnce` interfaces.
#[test]
#[timeout(30000)]
fn test_fn_mut_once_weakening_chain() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // Model a function that:
    //   requires: (*f).precondition(x) && (*f).postcondition_mut(x, ^f, r)
    //   ensures: f.postcondition_once(x, r)
    //
    // The precondition simulates having called FnMut::call_mut (which gives us
    // postcondition_mut), and the postcondition asks for FnOnce's postcondition_once.
    // The fn_mut_once law should connect them.

    // requires: (*f).postcondition_mut(x, ^f, r)
    let req_mut = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("r")],
    );

    // ensures: f.postcondition_once(x, r)
    let ens_once = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);

    let result = verify_function_with_modes(VerificationRequest::new(&[req_mut], &[ens_once]));

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "postcondition_mut should imply postcondition_once: {result:?}"
    );
}

/// Test that `postcondition_once` does NOT hold without the `fn_mut_once` law
/// when only `postcondition_mut` is assumed.
///
/// This is the negative case: without the law axiom, the two predicates
/// are independent uninterpreted functions with no connection.
#[test]
#[timeout(30000)]
fn test_fn_mut_once_without_law_fails() {
    // Manually construct an encoder WITHOUT calling assert_fn_mut_once_law
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare and assume postcondition_mut(f, x, f_final, r) = true
    let mut_call = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("r")],
    );
    let mut_term = encoder
        .encode_pure(&mut_call)
        .expect("encode postcondition_mut without law");
    encoder.assert_term(mut_term);

    // Try to prove postcondition_once(f, x, r)
    let once_call = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let once_term = encoder
        .encode_pure(&once_call)
        .expect("encode postcondition_once without law");

    // Negate and check: without the law, this should be SAT (not provable)
    let neg_once = encoder.solver.not(once_term);
    encoder.assert_term(neg_once);

    // Do NOT call assert_fn_mut_once_law — this is the control experiment
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Without fn_mut_once law, postcondition_once should be independent of postcondition_mut: {result:?}"
    );
}

/// Test the reverse direction: `postcondition_once` implies `postcondition_mut`
/// via the Skolem witness function.
///
/// The Skolemized reverse axiom provides:
///   `postcondition_once(f, x, result)` ==>
///     `postcondition_mut(f, x, witness(f, x, result), result)`
///
/// We verify that asserting `postcondition_once` AND negating `postcondition_mut`
/// at the Skolem witness value produces UNSAT — confirming the law forces
/// `postcondition_mut` to hold for the witness.
#[test]
#[timeout(30000)]
fn test_fn_mut_once_reverse_direction() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode postcondition_once(f, x, r) and assume it holds
    let once_call = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let once_term = encoder
        .encode_pure(&once_call)
        .expect("encode postcondition_once for reverse direction");
    encoder.assert_term(once_term);

    // We also need to declare postcondition_mut so the law can match
    let mut_call = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    let _mut_term = encoder
        .encode_pure(&mut_call)
        .expect("declare postcondition_mut for reverse direction");

    // Assert the fn_mut_once law (creates Skolem function and axioms)
    encoder.assert_fn_mut_once_law();

    // Now build postcondition_mut at the Skolem witness value.
    // The Skolem function is `fn_mut_once_witness_3_i_i_i(f, x, r)`.
    // Name includes sort signature to avoid collision (#507).
    let witness_decl = encoder
        .decls()
        .get_logic_func("fn_mut_once_witness_3_i_i_i");
    if let Some(witness_fn) = witness_decl.cloned() {
        let f_term = *encoder
            .vars_for_test()
            .get("f")
            .expect("variable 'f' should exist in encoder vars");
        let x_term = *encoder
            .vars_for_test()
            .get("x")
            .expect("variable 'x' should exist in encoder vars");
        let r_term = *encoder
            .vars_for_test()
            .get("r")
            .expect("variable 'r' should exist in encoder vars");
        let witness_val = encoder.solver.apply(&witness_fn, &[f_term, x_term, r_term]);

        // Build postcondition_mut(f, x, witness(f,x,r), r)
        let mut_decl_name = encoder
            .decls()
            .logic_func_names()
            .find(|k| k.starts_with("closure_postcondition_mut_"))
            .expect("postcondition_mut symbol should exist")
            .clone();
        let mut_fn = encoder
            .decls()
            .get_logic_func(&mut_decl_name)
            .expect("postcondition_mut function declaration should exist")
            .clone();
        let mut_at_witness = encoder
            .solver
            .apply(&mut_fn, &[f_term, x_term, witness_val, r_term]);

        // Negate: NOT postcondition_mut(f, x, witness(f,x,r), r)
        // If the law is correct, this should be UNSAT
        let neg = encoder.solver.not(mut_at_witness);
        encoder.assert_term(neg);

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "postcondition_once + reverse law should force postcondition_mut at witness: {result:?}"
        );
    } else {
        panic!(
            "Skolem function 'fn_mut_once_witness_3_i_i_i' not found in logic_funcs. \
             The fn_mut_once law should insert it during assert_fn_mut_once_law(). \
             Available logic_funcs: {:?}",
            encoder.decls().logic_func_names().collect::<Vec<_>>()
        );
    }
}

/// Test `fn_mut_once` law with a 2-argument closure (higher arity than default).
///
/// All existing tests use 1-arg closures (3-place `postcondition_once`, 4-place
/// `postcondition_mut`). This tests 2-arg closures:
///   `postcondition_once(f, x, y, result)` — 4-place
///   `postcondition_mut(f, x, y, ^f, result)` — 5-place
///
/// Part of #510 F3: missing multi-arity tests.
#[test]
#[timeout(30000)]
fn test_fn_mut_once_law_multi_arity_two_args() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // requires: (*f).postcondition_mut(x, y, ^f, r)
    let req_mut = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), var("y"), final_expr(var("f")), var("r")],
    );

    // ensures: f.postcondition_once(x, y, r)
    let ens_once = method_call(
        var("f"),
        "postcondition_once",
        vec![var("x"), var("y"), var("r")],
    );

    let result = verify_function_with_modes(VerificationRequest::new(&[req_mut], &[ens_once]));

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "2-arg postcondition_mut should imply postcondition_once: {result:?}"
    );
}

/// Test that two `postcondition_once` symbols with different signatures coexist
/// correctly in the same encoder.
///
/// Declares:
///   `postcondition_once_3_i_i_i` (1-arg Int closure)
///   `postcondition_once_3_i_b_i` (1-arg Bool closure)
/// and their corresponding `postcondition_mut` symbols.
///
/// The `fn_mut_once` law should create separate witness functions for each
/// signature and not confuse them.
///
/// Part of #510 F3: exposes potential witness name collision (#507).
#[test]
#[timeout(30000)]
fn test_fn_mut_once_law_multi_signature_coexistence() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // === First closure: 1-arg Int (signature i_i_i) ===
    let once_int = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_int)
        .expect("declare Int-sorted postcondition_once");

    let mut_int = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("r")],
    );
    encoder
        .encode_pure(&mut_int)
        .expect("declare Int-sorted postcondition_mut");

    // === Second closure: 1-arg Bool (signature i_b_i) ===
    let once_bool = method_call(
        var("g"),
        "postcondition_once",
        vec![bool_expr(true), var("r2")],
    );
    encoder
        .encode_pure(&once_bool)
        .expect("declare Bool-sorted postcondition_once");

    let mut_bool = method_call(
        deref(var("g")),
        "postcondition_mut",
        vec![bool_expr(true), var("s2"), var("r2")],
    );
    encoder
        .encode_pure(&mut_bool)
        .expect("declare Bool-sorted postcondition_mut");

    // Both postcondition_once symbols should exist with different signatures
    let once_count = encoder
        .decls()
        .logic_func_names()
        .filter(|k| k.starts_with("closure_postcondition_once_"))
        .count();
    assert_eq!(
        once_count, 2,
        "Expected two postcondition_once symbols (i_i_i and i_b_i)"
    );

    // Assert the law — should handle both signatures without collision
    encoder.assert_fn_mut_once_law();

    // Both witness functions should exist with distinct names
    let witness_int = encoder
        .decls()
        .has_logic_func("fn_mut_once_witness_3_i_i_i");
    let witness_bool = encoder
        .decls()
        .has_logic_func("fn_mut_once_witness_3_i_b_i");
    assert!(witness_int, "Expected witness for Int signature");
    assert!(witness_bool, "Expected witness for Bool signature");

    encoder
        .assert_eager_fn_mut_once_forward_instantiations(&[mut_int.clone(), mut_bool.clone()])
        .expect("eager forward instantiation should handle both signatures");

    // Check each signature in the same encoder. A raw SAT check over only the
    // quantified fn_mut_once axioms is solver-incomplete; these ground checks
    // verify the intended coexistence without accepting Unknown.
    let once_int_term = encoder
        .encode_pure(&once_int)
        .expect("encode Int once call for coexistence check");
    let not_once_int = encoder.solver.not(once_int_term);
    encoder.solver.push();
    encoder.assert_term(not_once_int);
    let int_result = encoder.check_sat();
    assert!(
        matches!(int_result, SolveResult::Unsat(_)),
        "Int fn_mut_once law should derive postcondition_once: {int_result:?}"
    );
    encoder.solver.pop();

    let once_bool_term = encoder
        .encode_pure(&once_bool)
        .expect("encode Bool once call for coexistence check");
    let not_once_bool = encoder.solver.not(once_bool_term);
    encoder.solver.push();
    encoder.assert_term(not_once_bool);
    let bool_result = encoder.check_sat();
    assert!(
        matches!(bool_result, SolveResult::Unsat(_)),
        "Bool fn_mut_once law should derive postcondition_once: {bool_result:?}"
    );
    encoder.solver.pop();
}
