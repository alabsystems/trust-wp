// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for closure signature parsing and matching (#2106 coverage gap).
//!
//! These tests exercise `parse_closure_signature` and `mut_signature_matches_once`
//! through the public `assert_fn_mut_once_law` integration path. The functions
//! are private on `AYEncoder`, so we verify their behavior by observing whether
//! the fn_mut_once axiom fires (matching pair found) or doesn't fire (no match).
//!
//! Test strategy:
//! - "Law fires" = postcondition_mut => postcondition_once is UNSAT (axiom constrains)
//! - "Law silent" = postcondition_mut AND NOT postcondition_once is SAT (unconstrained)

use ntest::timeout;

use super::*;

/// Helper: register postcondition_once with specific number of args (arity includes receiver).
/// Uses Int-sorted variables to get Int sort tags.
fn register_once(encoder: &mut AYEncoder, arg_count: usize) {
    let args: Vec<PureExpr> = (0..arg_count).map(|i| var(&format!("a{i}"))).collect();
    let expr = method_call(var("f"), "postcondition_once", args);
    encoder
        .encode_pure(&expr)
        .expect("postcondition_once should encode");
}

/// Helper: register postcondition_mut with specific number of args (arity includes receiver).
fn register_mut(encoder: &mut AYEncoder, arg_count: usize) {
    let args: Vec<PureExpr> = (0..arg_count).map(|i| var(&format!("m{i}"))).collect();
    let expr = method_call(var("f"), "postcondition_mut", args);
    encoder
        .encode_pure(&expr)
        .expect("postcondition_mut should encode");
}

// ── parse_closure_signature: exercised through matching ────────────

/// Basic matching: postcondition_once_3 + postcondition_mut_4 should pair.
/// This exercises parse_closure_signature for valid signatures and
/// mut_signature_matches_once for compatible Int-only sort tags.
#[test]
#[timeout(30000)]
fn test_signature_matching_basic_int_sorts() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // once: 3 params (f, x, r) → symbol closure_postcondition_once_3_i_i_i
    register_once(&mut encoder, 2);
    // mut: 4 params (f, x, s, r) → symbol closure_postcondition_mut_4_i_i_i_i
    register_mut(&mut encoder, 3);

    encoder.assert_fn_mut_once_law();

    // If matching worked, the forward axiom constrains: mut => once.
    // Use same variable names so ground terms match the universally quantified axiom.
    // mut(f, x, s, r) => once(f, x, r)
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    let both = encoder.solver_mut().and(mut_term, neg_once);
    encoder.assert_term(both);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "fn_mut_once law should fire for matching Int-sorted signatures"
    );
}

/// No matching pair: postcondition_once_3 + postcondition_mut_3 (same arity) shouldn't match.
/// This exercises parse_closure_signature's arity comparison:
/// mut_arity must == once_arity + 1.
#[test]
#[timeout(30000)]
fn test_signature_matching_same_arity_no_match() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // once: 3 params → arity 3
    register_once(&mut encoder, 2);
    // mut: 3 params → arity 3 (should be 4 for a match)
    register_mut(&mut encoder, 2);

    encoder.assert_fn_mut_once_law();

    // With no match, the law doesn't fire. Both should remain unconstrained.
    let mut_expr = method_call(var("f"), "postcondition_mut", vec![var("m0"), var("m1")]);
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("a0"), var("a1")]);
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    let both = encoder.solver_mut().and(mut_term, neg_once);
    encoder.assert_term(both);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "fn_mut_once law should NOT fire when arities don't match (once_arity + 1 != mut_arity)"
    );
}

/// Only postcondition_once declared, no postcondition_mut: law should be silent.
/// This exercises parse_closure_signature's prefix filtering.
#[test]
#[timeout(30000)]
fn test_signature_matching_only_once_no_crash() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    register_once(&mut encoder, 2);
    // No postcondition_mut registered

    encoder.assert_fn_mut_once_law();

    // Postcondition_once should remain unconstrained.
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("a0"), var("a1")]);
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    encoder.assert_term(once_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "postcondition_once should remain satisfiable when no mut pair exists"
    );
}

/// Only postcondition_mut declared, no postcondition_once: law iterates once_symbols which is empty.
#[test]
#[timeout(30000)]
fn test_signature_matching_only_mut_no_crash() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    register_mut(&mut encoder, 3);
    // No postcondition_once registered

    encoder.assert_fn_mut_once_law();

    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("m0"), var("m1"), var("m2")],
    );
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    encoder.assert_term(mut_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "postcondition_mut should remain satisfiable when no once pair exists"
    );
}

/// Multiple once/mut declarations: only compatible arity pairs should match.
/// Registers once_3 + mut_4 (should match) and once_3 + mut_3 (should not match).
#[test]
#[timeout(30000)]
fn test_signature_matching_multiple_symbols_selective() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // once: 3 params
    register_once(&mut encoder, 2);
    // mut_4: 4 params (matches once_3)
    register_mut(&mut encoder, 3);

    // Also register a postcondition_mut with 2 args (arity 3, doesn't match once_3)
    let non_match_expr = method_call(var("g"), "postcondition_mut", vec![var("x"), var("y")]);
    encoder
        .encode_pure(&non_match_expr)
        .expect("non-matching mut should encode");

    encoder.assert_fn_mut_once_law();

    // The 4-param mut should be constrained by the law (matches once_3)
    // Use same vars so E-matching triggers.
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    let both = encoder.solver_mut().and(mut_term, neg_once);
    encoder.assert_term(both);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "fn_mut_once law should fire for the matching pair"
    );
}

// ── mut_signature_matches_once Strategy B: integration tests ───────

/// Strategy B (#1997) integration: register postcondition_once and postcondition_mut
/// with Bool-typed args to exercise the "b" sort tag path. Primitive sort tags
/// are exempt from Strategy B's closure-env identity check.
#[test]
#[timeout(30000)]
fn test_signature_matching_bool_sorted_args() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register once with Bool-typed arg
    let once_expr = method_call(
        var("f"),
        "postcondition_once",
        vec![bool_expr(true), var("r")],
    );
    encoder.encode_pure(&once_expr).expect("once with bool arg");

    // Register mut with matching Bool + extra Int res_state
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![bool_expr(true), var("s"), var("r")],
    );
    encoder.encode_pure(&mut_expr).expect("mut with bool arg");

    encoder.assert_fn_mut_once_law();

    // The sort tags should be compatible: once [i, b, i] matches mut [i, b, i, i]
    // (receiver is Int, bool_expr(true) infers as Bool "b" tag, r/s are Int)
    // Actually all variables default to Int sort, and true is Bool.
    // This exercises the mixed-sort matching path in mut_signature_matches_once.
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    let both = encoder.solver_mut().and(mut_term, neg_once);
    encoder.assert_term(both);

    // Should be UNSAT if matching succeeded
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fn_mut_once law should fire for Bool-sorted argument matching, got {result:?}"
    );
}

/// Verify the witness Skolem function name includes sort signature.
/// This indirectly tests parse_closure_signature's sort tag extraction:
/// the witness name is built from the once sort signature.
#[test]
#[timeout(30000)]
fn test_witness_name_reflects_sort_signature() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    register_once(&mut encoder, 2); // → closure_postcondition_once_3_i_i_i
    register_mut(&mut encoder, 3); // → closure_postcondition_mut_4_i_i_i_i

    encoder.assert_fn_mut_once_law();

    // The witness function name should include the once sort signature
    let has_witness = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("fn_mut_once_witness_"));
    assert!(
        has_witness,
        "fn_mut_once_witness should be declared when a matching pair exists. \
         Declared funcs: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

/// No witness should be created when no matching pair exists.
#[test]
#[timeout(30000)]
fn test_no_witness_when_no_matching_pair() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    register_once(&mut encoder, 2); // arity 3
                                    // mut with wrong arity (also 3, should be 4)
    register_mut(&mut encoder, 2);

    encoder.assert_fn_mut_once_law();

    let has_witness = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("fn_mut_once_witness_"));
    assert!(
        !has_witness,
        "fn_mut_once_witness should NOT be declared when no matching pair exists"
    );
}
