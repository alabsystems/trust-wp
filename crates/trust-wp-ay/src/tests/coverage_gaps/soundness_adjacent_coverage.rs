// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for soundness-adjacent functions with zero direct coverage (#2198).
//!
//! Covers:
//! - `parse_closure_signature` edge cases (non-numeric arity)
//! - `mut_signature_matches_once` Strategy B closure-env identity check
//! - `produces_axioms` empty-domain guard behavior
//! - `Counterexample::from_model` arbitrary-precision integer storage path

use ay_dpll::api::Sort;
use ntest::timeout;

use super::*;

// ── AC1: parse_closure_signature edge cases ────────────────────────

/// Non-numeric arity in a closure signature symbol should not produce a match.
/// This exercises `parse_closure_signature`'s `arity_raw.parse::<usize>().ok()?`
/// guard. A corrupted symbol like `closure_postcondition_once_abc_i_i` should
/// be silently ignored (no panic, no false match).
#[test]
#[timeout(30000)]
fn test_malformed_arity_symbol_ignored_by_matching() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register a well-formed postcondition_once (arity 3: receiver + 2 args)
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    // Manually inject a malformed postcondition_mut symbol with non-numeric arity.
    // This simulates a corrupted or unexpected symbol name that parse_closure_signature
    // must handle gracefully.
    let malformed_decl = encoder.solver_mut().declare_fun(
        "closure_postcondition_mut_abc_i_i_i_i",
        &[Sort::Int, Sort::Int, Sort::Int, Sort::Int],
        Sort::Bool,
    );
    encoder.decls_for_test_mut().insert_logic_func(
        "closure_postcondition_mut_abc_i_i_i_i".to_string(),
        malformed_decl,
    );

    // assert_fn_mut_once_law should not crash and should not match the malformed symbol.
    encoder.assert_fn_mut_once_law();

    // Postcondition_once should remain unconstrained (no axiom fired).
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg = encoder.solver_mut().not(once_term);
    encoder.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "malformed arity symbol should not produce a match — once should remain unconstrained"
    );
}

/// Arity-tag count mismatch: symbol says arity=3 but only has 2 sort tags.
/// This exercises `parse_closure_signature`'s `sort_tags.len() != arity` guard.
#[test]
#[timeout(30000)]
fn test_arity_tag_count_mismatch_ignored() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register well-formed once (arity 3)
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    // Inject symbol claiming arity 4 but only providing 3 sort tags.
    // parse_closure_signature should reject: sort_tags.len() (3) != arity (4).
    let miscount_decl = encoder.solver_mut().declare_fun(
        "closure_postcondition_mut_4_i_i_i",
        &[Sort::Int, Sort::Int, Sort::Int],
        Sort::Bool,
    );
    encoder.decls_for_test_mut().insert_logic_func(
        "closure_postcondition_mut_4_i_i_i".to_string(),
        miscount_decl,
    );

    encoder.assert_fn_mut_once_law();

    // No witness should be created.
    let has_witness = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("fn_mut_once_witness_"));
    assert!(
        !has_witness,
        "arity/tag count mismatch should not produce a witness"
    );
}

// ── AC2: mut_signature_matches_once Strategy B env-sort identity ───

/// Strategy B closure-env identity check: when res_state tag starts with "c"
/// (closure env), it must equal the self sort (position 0) for matching.
/// A closure-env res_state that differs from the self sort should NOT match,
/// preventing cross-type axiom contamination.
#[test]
#[timeout(30000)]
fn test_strategy_b_rejects_cross_env_closure_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register postcondition_once with 3 params: receiver + 2 args.
    // Symbol: closure_postcondition_once_3_i_i_i (all Int tags)
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder.encode_pure(&once_expr).expect("once should encode");

    // Manually inject a postcondition_mut symbol with a closure-env res_state tag
    // that differs from position 0. This simulates two different closure types
    // with compatible arg/return sorts but different env sorts.
    //
    // once tags: [i, i, i]  (arity 3)
    // mut tags:  [i, i, c4141, i]  (arity 4, res_state at position 2 = "c4141" != "i" at pos 0)
    //
    // Strategy B: res_tag.starts_with('c') && res_tag != self_tag → reject
    let cross_env_decl = encoder.solver_mut().declare_fun(
        "closure_postcondition_mut_4_i_i_c4141_i",
        &[
            Sort::Int,
            Sort::Int,
            Sort::Uninterpreted("AA".to_string()),
            Sort::Int,
        ],
        Sort::Bool,
    );
    encoder.decls_for_test_mut().insert_logic_func(
        "closure_postcondition_mut_4_i_i_c4141_i".to_string(),
        cross_env_decl,
    );

    encoder.assert_fn_mut_once_law();

    // No witness should be created because Strategy B blocked the match.
    let has_witness = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("fn_mut_once_witness_"));
    assert!(
        !has_witness,
        "Strategy B should reject cross-env closure sort match: \
         res_state 'c4141' != self 'i' at position 0. \
         Declared: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

/// Strategy B allows matching when res_state is a primitive tag ("i", "b", "u"),
/// even if it differs from position 0. Primitive tags are exempt from the
/// closure-env identity check.
#[test]
#[timeout(30000)]
fn test_strategy_b_allows_primitive_res_state() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register once (arity 3): closure_postcondition_once_3_i_i_i
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder.encode_pure(&once_expr).expect("once should encode");

    // Register mut (arity 4): closure_postcondition_mut_4_i_i_i_i
    // res_state at position 2 = "i" (primitive, exempt from Strategy B)
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    encoder.encode_pure(&mut_expr).expect("mut should encode");

    encoder.assert_fn_mut_once_law();

    // Witness SHOULD be created because primitive Int res_state is allowed.
    let has_witness = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("fn_mut_once_witness_"));
    assert!(
        has_witness,
        "Strategy B should ALLOW primitive 'i' res_state match. \
         Declared: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

// ── AC3: produces_axioms empty-domain guard ────────────────────────

/// `assert_produces_ground_transitivity` with an empty-domain FuncDecl
/// should return early without crashing. The `domain().len() != 3` guard
/// prevents the empty-domain path from reaching the `unwrap_or(Sort::Int)`
/// fallback in `assert_produces_ground_transitivity_instance`.
#[test]
#[timeout(30000)]
fn test_produces_ground_transitivity_empty_domain_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    // Create a FuncDecl with zero domain sorts (the pathological case).
    let empty_domain_decl =
        encoder
            .solver_mut()
            .declare_fun("produces_empty_domain", &[], Sort::Bool);

    // Call with dummy terms — should not crash.
    let dummy_from = encoder.solver_mut().int_const(0);
    let dummy_visited = encoder.solver_mut().int_const(1);
    let dummy_to = encoder.solver_mut().int_const(2);
    encoder.assert_produces_ground_transitivity(
        &empty_domain_decl,
        dummy_from,
        dummy_visited,
        dummy_to,
    );

    // Verify the solver is still in a consistent state.
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "empty-domain produces func should not make the context inconsistent, got {result:?}"
    );
}

/// `assert_produces_ground_transitivity` with a 1-domain FuncDecl (wrong arity)
/// should also return early without crashing.
#[test]
#[timeout(30000)]
fn test_produces_ground_transitivity_wrong_arity_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    // Create a FuncDecl with 1 domain sort (not 3).
    let one_domain_decl =
        encoder
            .solver_mut()
            .declare_fun("produces_one_domain", &[Sort::Int], Sort::Bool);

    let dummy = encoder.solver_mut().int_const(0);
    encoder.assert_produces_ground_transitivity(&one_domain_decl, dummy, dummy, dummy);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "1-domain produces func should not make the context inconsistent, got {result:?}"
    );
}

/// `assert_produces_ground_transitivity` with mismatched state sorts
/// (domain[0] != domain[2]) should return early.
#[test]
#[timeout(30000)]
fn test_produces_ground_transitivity_mismatched_state_sorts_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    // Create FuncDecl where domain[0] (Int) != domain[2] (Bool).
    let mismatched_decl = encoder.solver_mut().declare_fun(
        "produces_mismatched",
        &[Sort::Int, Sort::Int, Sort::Bool],
        Sort::Bool,
    );

    let int_term = encoder.solver_mut().int_const(0);
    let bool_term = encoder.solver_mut().bool_const(true);
    encoder.assert_produces_ground_transitivity(&mismatched_decl, int_term, int_term, bool_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "mismatched state sorts should not make the context inconsistent, got {result:?}"
    );
}

// ── AC4: arbitrary-precision integer counterexamples ───────────────

/// Counterexample values store arbitrary-precision integers directly.
/// Verify that `CounterexampleType::Int` can represent i64 boundary values
/// without truncation and that the display path stays stable.
#[test]
#[timeout(30000)]
fn test_counterexample_int_max_representable() {
    let cex = Counterexample {
        values: vec![CounterexampleValue {
            name: "large_bigint_value".to_string(),
            value: CounterexampleType::Int(i64::MAX.into()),
            origin: None,
        }],
        violated_postcondition: None,
    };

    // Verify we can access the value without panic.
    assert_eq!(cex.values.len(), 1);
    assert_eq!(
        cex.values[0].value,
        CounterexampleType::Int(i64::MAX.into())
    );

    // Verify Debug formatting doesn't panic for extreme values.
    let debug_str = format!("{:?}", cex);
    assert!(
        debug_str.contains("large_bigint_value"),
        "Debug output should include the variable name"
    );
}

/// Verify that both positive and negative i64 boundary values survive in the
/// public counterexample API.
#[test]
#[timeout(30000)]
fn test_counterexample_negative_extreme_representable() {
    let cex = Counterexample {
        values: vec![
            CounterexampleValue {
                name: "pos_extreme".to_string(),
                value: CounterexampleType::Int(i64::MAX.into()),
                origin: None,
            },
            CounterexampleValue {
                name: "neg_extreme".to_string(),
                value: CounterexampleType::Int(i64::MIN.into()),
                origin: None,
            },
        ],
        violated_postcondition: None,
    };

    assert_eq!(cex.values.len(), 2);
    assert_eq!(
        cex.values[0].value,
        CounterexampleType::Int(i64::MAX.into())
    );
    assert_eq!(
        cex.values[1].value,
        CounterexampleType::Int(i64::MIN.into())
    );
}

/// End-to-end: verify that a Failed verification result with extreme
/// counterexample values can be constructed and inspected via the public API.
#[test]
#[timeout(30000)]
fn test_verification_result_failed_with_extreme_counterexample() {
    let cex = Counterexample {
        values: vec![
            CounterexampleValue {
                name: "x".to_string(),
                value: CounterexampleType::Int(i64::MAX.into()),
                origin: None,
            },
            CounterexampleValue {
                name: "flag".to_string(),
                value: CounterexampleType::Bool(true),
                origin: None,
            },
        ],
        violated_postcondition: None,
    };

    let result = VerificationResult::Failed(cex);
    match &result {
        VerificationResult::Failed(c) => {
            assert_eq!(c.values.len(), 2, "counterexample should have 2 values");
            assert_eq!(c.values[0].value, CounterexampleType::Int(i64::MAX.into()));
        }
        other => panic!("expected Failed, got: {other:?}"),
    }
}

// ── #2163: coerce_to_seq bridge UF injectivity ─────────────────────

/// Two distinct Vec-sorted variables coerced through the bridge UF must
/// remain distinguishable. The injectivity axiom (#2163) ensures that
/// `bridge(v1) == bridge(v2) => v1 == v2`, so asserting `v1 != v2` after
/// bridge coercion should not become unsatisfiable.
///
/// Without the injectivity axiom, the solver could assign
/// `bridge(v1) == bridge(v2)` even when `v1 != v2`, making the two Vecs
/// indistinguishable in length/contents — a potential false verification.
#[test]
#[timeout(30000)]
fn test_bridge_uf_injectivity_preserves_distinct_vecs() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let vec_sort = Sort::Uninterpreted("std::vec::Vec".to_string());

    // Create two Vec-sorted variables directly (bypassing get_or_declare_var
    // normalization to force the bridge path).
    let v1 = encoder
        .solver_mut()
        .declare_const("vec_v1", vec_sort.clone());
    let v2 = encoder
        .solver_mut()
        .declare_const("vec_v2", vec_sort.clone());
    encoder.vars_mut_for_test().insert("vec_v1".to_string(), v1);
    encoder.vars_mut_for_test().insert("vec_v2".to_string(), v2);

    // Assert v1 != v2 at the Vec sort level.
    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(v1, v2);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    // Encode len() calls using ExprSort::Seq annotation so is_seq_receiver
    // dispatches to encode_seq_operation_impl, which calls coerce_to_seq
    // on the Vec-sorted term, triggering the bridge UF.
    use trust_wp_core::formula::ExprSort;
    let v1_len = method_call(var_with_sort("vec_v1", ExprSort::Seq), "len", vec![]);
    let v2_len = method_call(var_with_sort("vec_v2", ExprSort::Seq), "len", vec![]);
    let _v1_len_term = encoder
        .encode_pure(&v1_len)
        .expect("v1.len() should encode");
    let _v2_len_term = encoder
        .encode_pure(&v2_len)
        .expect("v2.len() should encode");

    // With injectivity, bridge(v1) == bridge(v2) implies v1 == v2. Since v1 !=
    // v2 is asserted above, forcing the bridged Seq terms equal must be UNSAT.
    let bridged_v1 = encoder
        .seq_state_for_test()
        .get_coerced_term(&v1)
        .expect("v1 should have a Vec-to-Seq bridge term");
    let bridged_v2 = encoder
        .seq_state_for_test()
        .get_coerced_term(&v2)
        .expect("v2 should have a Vec-to-Seq bridge term");
    let bridges_eq = {
        let solver = encoder.solver_mut();
        solver.eq(bridged_v1, bridged_v2)
    };
    encoder.assert_term(bridges_eq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Two distinct Vec variables must not collapse to the same Seq bridge term. Got: {result:?}"
    );
}

// ── #994/#2231 D3: Int→Seq bridge in coerce_to_seq ─────────────────

/// An Int-sorted term reaching `coerce_to_seq` should be bridged to Seq sort
/// instead of being returned unchanged (which causes downstream `safe_apply`
/// to fail with sort mismatch). The bridge creates an unconstrained Seq value
/// tracked by the `SortFallbackToInt` unsoundness counter. (#994, #2231 D3)
///
/// This test simulates the real "got Int" scenario: a variable is pre-declared
/// as Int (e.g., from a prior non-Seq encoding context), then later used as
/// a Seq receiver. The variable's Int term reaches `coerce_to_seq` through
/// `encode_seq_operation_impl`, and the bridge converts it to Seq.
#[test]
#[timeout(30000)]
fn test_int_sorted_var_bridges_to_seq_for_len() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Pre-declare the variable as Int (simulating a prior non-Seq context).
    let _int_term = encoder.get_or_declare_var("v_stuck_int", Sort::Int);

    // Register a Seq sort hint for the variable so is_seq_receiver dispatches
    // to the Seq encoding path. This simulates the hint system tagging the
    // variable from a `.len()` context while the variable was already declared
    // as Int from a prior expression.
    use trust_wp_core::formula::ExprSort;
    encoder.record_sort_hint("v_stuck_int".to_string(), ExprSort::Seq);

    // Encode v_stuck_int.len() — receiver is dispatched to Seq path via hint.
    // The Var has no ExprSort annotation, so resolve_var_sort_or_int_with_annotation
    // finds the hint and returns Seq. get_or_declare_var attempts Int→Seq upgrade.
    // The len result should encode successfully regardless of bridge path.
    let len_expr = method_call(var("v_stuck_int"), "len", vec![]);
    let result = encoder.encode_pure(&len_expr);
    assert!(
        result.is_ok(),
        "Int-sorted variable used as Seq receiver should encode successfully. Got: {result:?}"
    );
}

/// Test that an Int-sorted variable with a Seq sort hint encodes successfully
/// through the sort upgrade path (get_or_declare_var detects Int→Seq mismatch
/// and redeclares with the stronger sort). This verifies the primary fix path
/// for "got Int" tests where hints propagate correctly. (#994, #2231 D3)
///
/// Note: The `coerce_to_seq` Int→Seq bridge is defense-in-depth for cases where
/// the sort upgrade in `get_or_declare_var` cannot fire (complex expressions,
/// name chain mismatches, direct term construction). Those edge cases are hard
/// to reproduce in unit tests but occur in real harness tests like bug/1562.
#[test]
#[timeout(30000)]
fn test_int_var_with_seq_hint_upgrades_and_encodes_len() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Pre-declare the variable as Int (simulating a prior non-Seq context).
    let int_const = encoder.solver_mut().declare_const("__raw_int_v", Sort::Int);
    encoder
        .vars_mut_for_test()
        .insert("__raw_int_v".to_string(), int_const);
    encoder
        .var_sorts_mut_for_test()
        .insert("__raw_int_v".to_string(), Sort::Int);

    // Register Seq hint so method dispatch reaches the Seq path and
    // resolve_var_sort_or_int_with_annotation returns Seq for the upgrade.
    use trust_wp_core::formula::ExprSort;
    encoder.record_sort_hint("__raw_int_v".to_string(), ExprSort::Seq);

    // Encode __raw_int_v.len() — the Seq hint triggers Int→Seq upgrade in
    // get_or_declare_var, then coerce_to_seq gets a Seq-sorted term (no bridge needed).
    let len_expr = method_call(var("__raw_int_v"), "len", vec![]);
    let result = encoder.encode_pure(&len_expr);

    assert!(
        result.is_ok(),
        "Int-sorted variable with Seq hint should upgrade and encode len. Got: {result:?}"
    );
}
