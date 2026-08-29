// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;

use super::*;

// =============================================================================
// axiom_apply_sort_adapted tests (Part of #2556)
//
// When postcondition/postcondition_mut/postcondition_once UF declarations have
// divergent domain sorts (due to hybrid inferred/actual sort resolution in
// encode_closure_spec_method), axiom_apply_tracked returns None and the axiom
// is skipped. `axiom_apply_sort_adapted` historically fabricated a second
// declaration with the same name and adapted sorts; AY 0.2 correctly rejects
// that unauthenticated identity. The compatibility entry point now fails closed
// and records the conservative premise-axiom skip.
// =============================================================================

/// Domain divergence must not mint a differently typed handle for an existing
/// function symbol.
#[test]
#[timeout(30000)]
fn test_sort_adapted_apply_rejects_sort_divergence() {
    unsoundness::reset();
    let mut encoder = AYEncoder::new();
    // Declare f: (Uninterpreted("ClosureEnv"), Int) -> Bool
    let env_sort = Sort::Uninterpreted("ClosureEnv_test".to_string());
    let func = encoder.solver.declare_fun(
        "closure_postcondition_test",
        &[env_sort.clone(), Sort::Int],
        Sort::Bool,
    );
    // No register_logic_func needed — axiom_apply uses the FuncDecl directly

    // Create args with DIFFERENT sorts: (Int, Int) — simulating vars created
    // from a partner declaration that resolved to Sort::Int for the self param
    let arg0 = encoder.solver.fresh_var("self_int", Sort::Int);
    let arg1 = encoder.solver.fresh_var("x_int", Sort::Int);
    let args = [arg0, arg1];

    // The strict application fails due to sort mismatch (Int vs ClosureEnv).
    let strict_result = encoder.axiom_apply("test:strict", &func, &args);
    assert!(
        strict_result.is_none(),
        "axiom_apply_tracked should return None on sort mismatch"
    );

    // The compatibility path must fail closed rather than fabricating a new
    // declaration under `closure_postcondition_test`.
    let adapted_result = encoder.axiom_apply_sort_adapted("test:adapted", &func, &args);
    assert!(
        adapted_result.is_none(),
        "sort divergence must not authorize a differently typed function handle"
    );
    assert_eq!(
        unsoundness::snapshot().get(&UnsoundnessCategory::ClosureAxiomSkipped),
        Some(&1),
        "the omitted premise axiom must remain visible in the honesty counter"
    );
    unsoundness::reset();
}

/// axiom_apply_sort_adapted uses the fast path when sorts already match.
#[test]
#[timeout(30000)]
fn test_sort_adapted_apply_fast_path_matching_sorts() {
    let mut encoder = AYEncoder::new();
    let func = encoder
        .solver
        .declare_fun("test_fn", &[Sort::Int, Sort::Int], Sort::Bool);
    // No register_logic_func needed — axiom_apply uses the FuncDecl directly

    let arg0 = encoder.solver.fresh_var("a", Sort::Int);
    let arg1 = encoder.solver.fresh_var("b", Sort::Int);
    let args = [arg0, arg1];

    // Both paths should succeed when sorts match
    let tracked = encoder.axiom_apply_tracked("test:tracked", &func, &args);
    assert!(tracked.is_some());

    let adapted = encoder.axiom_apply_sort_adapted("test:adapted", &func, &args);
    assert!(adapted.is_some());
}

/// axiom_apply_sort_adapted returns None on arity mismatch (not a sort issue).
#[test]
#[timeout(30000)]
fn test_sort_adapted_apply_arity_mismatch_returns_none() {
    let mut encoder = AYEncoder::new();
    let func = encoder
        .solver
        .declare_fun("test_fn", &[Sort::Int, Sort::Int], Sort::Bool);
    // No register_logic_func needed — axiom_apply uses the FuncDecl directly

    let arg0 = encoder.solver.fresh_var("a", Sort::Int);
    // Only 1 arg for a 2-arg function — arity mismatch
    let result = encoder.axiom_apply_sort_adapted("test:arity", &func, &[arg0]);
    assert!(result.is_none(), "arity mismatch should still return None");
}

// =============================================================================
// Fn closure law tests (Phase 4, Part of #358)
//
// The Fn closure laws connect the Fn-trait `postcondition` to
// `postcondition_mut` and `postcondition_once`:
//
//   fn_mut law:  postcondition_mut(self, args, res_state, result)
//                  = (postcondition(self, args, result) && self == res_state)
//   fn_once law: postcondition_once(self, args, result)
//                  = (postcondition(self, args, result) && resolve(self))
//   fn_hist_inv: hist_inv(self, res_state) = (self == res_state)
//   postcondition_mut_hist_inv: postcondition_mut(...) ==> hist_inv(self, res_state)
// =============================================================================

/// Test that fn closure laws are asserted when postcondition, `postcondition_mut`,
/// and `postcondition_once` symbols are all declared.
#[test]
#[timeout(30000)]
fn test_fn_closure_laws_asserted() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare postcondition(f, x, result) — Fn-trait three-place
    let post_call = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition symbol");

    // Declare postcondition_mut(f, x, ^f, result) — four-place
    let mut_call = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("r")],
    );
    encoder
        .encode_pure(&mut_call)
        .expect("declare postcondition_mut symbol");

    // Declare postcondition_once(f, x, result) — three-place
    let once_call = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once symbol");

    // Assert the laws — should not panic and should not introduce contradictions
    encoder.assert_fn_closure_laws();

    // Semantic check: postcondition + (f == f') should imply postcondition_mut
    // via fn_mut law: postcondition_mut(f, x, f', r) <==> postcondition(f, x, r) && f == f'
    let post_term = encoder
        .encode_pure(&post_call)
        .expect("encode postcondition for fn_mut check");
    let f_var = encoder.encode_pure(&var("f")).expect("encode var f");
    let f_final = encoder
        .encode_pure(&final_expr(var("f")))
        .expect("encode final(f)");
    let f_eq_f_final = encoder.solver.eq(f_var, f_final);
    let mut_term = encoder
        .encode_pure(&mut_call)
        .expect("encode postcondition_mut for fn_mut check");

    // Assume postcondition(f, x, r) AND f == ^f, then negate postcondition_mut
    encoder.assert_term(post_term);
    encoder.assert_term(f_eq_f_final);
    let neg_mut = encoder.solver.not(mut_term);
    encoder.assert_term(neg_mut);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fn_closure_laws fn_mut direction: postcondition + (f==f') ==> postcondition_mut should hold: {result:?}"
    );
}

/// Test that fn closure laws are a no-op when only postcondition is declared
/// without matching `postcondition_mut/postcondition_once`.
#[test]
#[timeout(30000)]
fn test_fn_closure_laws_noop_without_mut_or_once() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Only declare postcondition
    let post_call = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition for noop test");

    // Should be a no-op (no matching mut/once symbols)
    encoder.assert_fn_closure_laws();

    // Solver should still be satisfiable
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Should be SAT when law is no-op: {result:?}"
    );
}

/// Test that a missing `postcondition_mut` companion is synthesized from the
/// selected `postcondition` declaration.
#[test]
#[timeout(30000)]
fn test_fn_closure_laws_synthesizes_missing_mut_companion() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let post_call = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition for synthesis test");
    encoder
        .get_or_declare_var("x_current", ay_dpll::api::Sort::Int)
        .expect("declare mut-borrow state var");
    encoder
        .get_or_declare_var("x_final", ay_dpll::api::Sort::Int)
        .expect("declare mut-borrow final var");

    encoder.assert_fn_closure_laws();

    assert!(
        encoder.has_closure_postcondition_mut_symbols(),
        "fn closure laws should synthesize the matching mut companion when absent"
    );
}

/// Test the Fn -> `FnMut` weakening: postcondition implies `postcondition_mut`
/// when self == `res_state`.
///
/// Given:
///   - postcondition(f, x, result) holds (Fn trait)
/// Prove:
///   - `postcondition_mut(f, x, f, result)` holds (self == `res_state` via `fn_mut` law)
///
/// This is the Fn -> `FnMut` step of the weakening chain.
#[test]
#[timeout(30000)]
fn test_fn_to_fnmut_weakening() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // Model: requires f.postcondition(x, result), ensures (*f).postcondition_mut(x, ^f, result)
    // The fn_mut law says postcondition_mut(f, x, f', r) = (postcondition(f, x, r) && f == f')
    // In the ensures, res_state = ^f. For an Fn closure, ^f == *f (self == res_state).
    // But we can't use that directly — instead, we'll test the chain through verify_function.

    // requires: f.postcondition(x, result)
    let req = method_call(var("f"), "postcondition", vec![var("x"), var("result")]);

    // Also require: f == f_state (self == res_state, modeling Fn invariant)
    let req_eq = eq(var("f"), var("f_state"));

    // ensures: (*f).postcondition_mut(x, f_state, result)
    let ens = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), var("f_state"), var("result")],
    );

    // Provide return_expr so result_binding doesn't fire SortFallbackToInt
    // for missing body when postconditions reference `result`. (#2566)
    let return_e = var("result");
    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, req_eq], &[ens]).return_expr(Some(&return_e)),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "postcondition + (self == res_state) should imply postcondition_mut via fn_mut law: {result:?}"
    );
}

/// Test the Fn -> `FnOnce` weakening: postcondition implies `postcondition_once`.
///
/// Given:
///   - postcondition(f, x, result) holds (Fn trait)
/// Prove:
///   - `postcondition_once(f, x, result)` holds (via `fn_once` law + trivial resolve)
///
/// The `fn_once` law says: `postcondition_once` = (postcondition && resolve(self))
/// For Int-sorted closure env, resolve is trivially true.
#[test]
#[timeout(30000)]
fn test_fn_to_fnonce_weakening() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // requires: f.postcondition(x, result)
    let req = method_call(var("f"), "postcondition", vec![var("x"), var("result")]);

    // ensures: f.postcondition_once(x, result)
    let ens = method_call(
        var("f"),
        "postcondition_once",
        vec![var("x"), var("result")],
    );

    // Provide return_expr so result_binding doesn't fire SortFallbackToInt
    // for missing body when postconditions reference `result`. (#2566)
    let return_e = var("result");
    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&return_e)),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "postcondition should imply postcondition_once via fn_once law: {result:?}"
    );
}

/// Test the full Fn -> `FnMut` -> `FnOnce` weakening chain.
///
/// This models the `06_fn_specs.rs` pattern:
///   `weaken_std` (Fn) -> `weaken_2_std` (`FnMut`) -> `weaken_3_std` (`FnOnce`)
///
/// Given: postcondition(f, x, result) (Fn ensures)
/// Prove: `postcondition_once(f, x, result)` (`FnOnce` ensures)
///
/// Requires both `fn_mut` law + `fn_mut_once` law (or `fn_once` law directly).
#[test]
#[timeout(30000)]
fn test_full_fn_weakening_chain() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // requires: f.postcondition(x, result) — Fn ensures this
    let req = method_call(var("f"), "postcondition", vec![var("x"), var("result")]);

    // ensures: f.postcondition_once(x, result) — FnOnce needs this
    let ens = method_call(
        var("f"),
        "postcondition_once",
        vec![var("x"), var("result")],
    );

    // Provide return_expr so result_binding doesn't fire SortFallbackToInt
    // for missing body when postconditions reference `result`. (#2566)
    let return_e = var("result");
    // This exercises the full chain: postcondition -> fn_once law -> postcondition_once
    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&return_e)),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Full Fn -> FnOnce weakening chain should verify: {result:?}"
    );
}

/// Negative test: postcondition does NOT imply `postcondition_once` without the laws.
#[test]
#[timeout(30000)]
fn test_fn_to_fnonce_fails_without_law() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare and assume postcondition(f, x, r) = true
    let post_call = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let post_term = encoder
        .encode_pure(&post_call)
        .expect("encode postcondition without law");
    encoder.assert_term(post_term);

    // Try to prove postcondition_once(f, x, r)
    let once_call = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let once_term = encoder
        .encode_pure(&once_call)
        .expect("encode postcondition_once without law");

    // Negate and check: without the law, this should be SAT (not provable)
    let neg_once = encoder.solver.not(once_term);
    encoder.assert_term(neg_once);

    // Do NOT call assert_fn_closure_laws — control experiment
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Without fn closure laws, postcondition_once should be independent: {result:?}"
    );
}

/// Test that `hist_inv` is declared and its identity axiom holds.
#[test]
#[timeout(30000)]
fn test_hist_inv_identity() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare postcondition and postcondition_mut to trigger hist_inv declaration
    let post_call = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition for hist_inv test");

    let mut_call = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("r")],
    );
    encoder
        .encode_pure(&mut_call)
        .expect("declare postcondition_mut for hist_inv test");

    // Assert the laws (creates hist_inv and its axioms)
    encoder.assert_fn_closure_laws();

    // hist_inv should now be declared
    let hist_inv_exists = encoder
        .decls()
        .logic_func_names()
        .any(|k| k.starts_with("closure_hist_inv_"));
    assert!(
        hist_inv_exists,
        "hist_inv should be declared by fn closure laws"
    );

    // The fn_hist_inv axiom says: hist_inv(a, b) = (a == b)
    // Test: assert a != b, then hist_inv(a, b) should be false
    let a = encoder
        .get_or_declare_var("a", Sort::Int)
        .expect("declare var 'a' as Int");
    let b = encoder
        .get_or_declare_var("b", Sort::Int)
        .expect("declare var 'b' as Int");

    let a_eq_b = encoder.solver.eq(a, b);
    let neq = encoder.solver.not(a_eq_b);
    encoder.assert_term(neq);

    // Look up hist_inv and apply it
    let hist_inv_name = encoder
        .decls()
        .logic_func_names()
        .find(|k| k.starts_with("closure_hist_inv_"))
        .expect("hist_inv symbol should exist")
        .clone();
    let hist_inv_fn = encoder
        .decls()
        .get_logic_func(&hist_inv_name)
        .expect("hist_inv function declaration should exist")
        .clone();
    let hist_term = encoder.solver.apply(&hist_inv_fn, &[a, b]);

    // Assert hist_inv(a, b) = true — should be UNSAT since a != b
    encoder.assert_term(hist_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "hist_inv(a, b) && a != b should be UNSAT: {result:?}"
    );
}

/// Test that `postcondition_mut ==> hist_inv(self, res_state)` implication holds.
///
/// The axiom `assert_fn_mut_law_and_hist_inv` (axioms.rs:420-436) asserts:
///   `forall f,x,s,r. postcondition_mut(f,x,s,r) ==> hist_inv(f,s)`
///
/// `test_hist_inv_identity` only tests the identity law (`hist_inv(a,b) = (a==b)`).
/// This test verifies the implication: asserting `postcondition_mut(f,x,s,r)`
/// should force `hist_inv(f,s)` to be true.
#[test]
#[timeout(30000)]
fn test_postcondition_mut_implies_hist_inv() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare postcondition(f, x, r) — Fn-trait three-place
    let post_call = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition for hist_inv implication test");

    // Declare postcondition_mut(f, x, ^f, r) — four-place
    let mut_call = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("r")],
    );
    encoder
        .encode_pure(&mut_call)
        .expect("declare postcondition_mut for hist_inv implication test");

    // Assert closure laws (creates hist_inv and both axioms)
    encoder.assert_fn_closure_laws();

    // Assert postcondition_mut(f, x, s, r) = true for ground terms
    let mut_term = encoder
        .encode_pure(&mut_call)
        .expect("encode postcondition_mut for ground assertion");
    encoder.assert_term(mut_term);

    // Look up hist_inv and apply it to (f, ^f) — the self and res_state positions
    let hist_inv_name = encoder
        .decls()
        .logic_func_names()
        .find(|k| k.starts_with("closure_hist_inv_"))
        .expect("hist_inv should be declared")
        .clone();
    let hist_inv_fn = encoder
        .decls()
        .get_logic_func(&hist_inv_name)
        .expect("hist_inv function declaration should exist")
        .clone();

    let f_var = encoder
        .encode_pure(&var("f"))
        .expect("encode var f for hist_inv check");
    let f_final = encoder
        .encode_pure(&final_expr(var("f")))
        .expect("encode final(f) for hist_inv check");
    let hist_term = encoder.solver.apply(&hist_inv_fn, &[f_var, f_final]);

    // Negate hist_inv(f, ^f) — should be UNSAT because postcondition_mut ==> hist_inv
    let neg_hist = encoder.solver.not(hist_term);
    encoder.assert_term(neg_hist);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "postcondition_mut(f,x,^f,r) && NOT hist_inv(f,^f) should be UNSAT: {result:?}"
    );
}

/// Test Fn -> `FnOnce` weakening with a 2-argument closure (higher arity).
///
/// All existing closure law tests use 1-arg closures. This tests 2-arg:
///   `postcondition(f, x, y, result)` — 4-place
///   `postcondition_once(f, x, y, result)` — 4-place
///
/// Part of #510 F3: missing multi-arity tests.
#[test]
#[timeout(30000)]
fn test_fn_closure_laws_multi_arity_two_args() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // requires: f.postcondition(x, y, result) — Fn trait with 2 args
    let req = method_call(
        var("f"),
        "postcondition",
        vec![var("x"), var("y"), var("result")],
    );

    // ensures: f.postcondition_once(x, y, result)
    let ens = method_call(
        var("f"),
        "postcondition_once",
        vec![var("x"), var("y"), var("result")],
    );

    // Provide return_expr so result_binding doesn't fire SortFallbackToInt
    // for missing body when postconditions reference `result`. (#2566)
    let return_e = var("result");
    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&return_e)),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "2-arg Fn -> FnOnce weakening should verify via fn_once law: {result:?}"
    );
}

/// Test Fn -> `FnMut` weakening with a Bool-sorted argument.
///
/// Verifies that the `fn_mut` law correctly handles mixed sorts in the
/// closure law axiom quantifier variables (#522 regression).
///
/// Part of #510 F3: missing multi-sort tests.
#[test]
#[timeout(30000)]
fn test_fn_closure_laws_bool_sorted_args() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // requires: f.postcondition(true, result) — Bool arg
    let req = method_call(
        var("f"),
        "postcondition",
        vec![bool_expr(true), var("result")],
    );

    // Also require f == f_state (Fn invariant: self not mutated)
    let req_eq = eq(var("f"), var("f_state"));

    // ensures: (*f).postcondition_mut(true, f_state, result)
    let ens = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![bool_expr(true), var("f_state"), var("result")],
    );

    // Provide return_expr so result_binding doesn't fire SortFallbackToInt
    // for missing body when postconditions reference `result`. (#2566)
    let return_e = var("result");
    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, req_eq], &[ens]).return_expr(Some(&return_e)),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Bool-sorted Fn -> FnMut weakening should verify via fn_mut law: {result:?}"
    );
}

/// Test Fn -> `FnMut` weakening with 2-argument closure.
///
/// Combines multi-arity with the `fn_mut` law. The law should correctly
/// generate the 5-place `postcondition_mut` symbol from 4-place postcondition.
///
/// Part of #510 F3: missing multi-arity tests.
#[test]
#[timeout(30000)]
fn test_fn_to_fnmut_weakening_multi_arity() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // requires: f.postcondition(x, y, result) — 2-arg Fn trait
    let req = method_call(
        var("f"),
        "postcondition",
        vec![var("x"), var("y"), var("result")],
    );

    // requires: f == f_state (Fn invariant)
    let req_eq = eq(var("f"), var("f_state"));

    // ensures: (*f).postcondition_mut(x, y, f_state, result)
    let ens = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), var("y"), var("f_state"), var("result")],
    );

    // Provide return_expr so result_binding doesn't fire SortFallbackToInt
    // for missing body when postconditions reference `result`. (#2566)
    let return_e = var("result");
    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, req_eq], &[ens]).return_expr(Some(&return_e)),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "2-arg Fn -> FnMut weakening should verify via fn_mut law: {result:?}"
    );
}

/// Diagnostic: test fn_once law with push/pop scope mimicking pipeline's
/// two-phase solve pattern. The axiom-free probe pops before axioms,
/// and the full axiom path reasserts the negated goal in a nested scope.
#[test]
#[timeout(30000)]
fn test_fn_once_law_with_scope_nesting() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Step 1: Encode and assert requires
    let post_call = method_call(var("f"), "postcondition", vec![var("x"), var("result")]);
    let post_term = encoder
        .encode_pure(&post_call)
        .expect("encode postcondition");
    encoder.assert_term(post_term);

    // Step 2: Encode negated ensure (declares postcondition_once UF)
    let once_call = method_call(
        var("f"),
        "postcondition_once",
        vec![var("x"), var("result")],
    );
    let once_term = encoder
        .encode_pure(&once_call)
        .expect("encode postcondition_once");
    let neg_once = encoder.solver.not(once_term);

    // Step 3: Axiom-free probe (push, assert negated, check, pop)
    encoder.push_scope().expect("push axiom-free scope");
    encoder.assert_term(neg_once);
    let _probe_result = encoder.check_sat(); // should be SAT (no axioms)
    encoder.pop_scope().expect("pop axiom-free scope");

    // Step 4: Assert axioms
    encoder.assert_fn_closure_laws();

    // Step 5: Full axiom path (push, assert negated, check)
    encoder.push_scope().expect("push full-axiom scope");
    encoder.assert_term(neg_once);
    let result = encoder.check_sat();
    encoder.pop_scope().expect("pop full-axiom scope");

    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fn_once law with scope nesting should be UNSAT: {result:?}"
    );
}

/// Diagnostic: direct encoder test mimicking pipeline order for fn_once law.
/// This bypasses verify_function_with_modes to isolate whether the issue is
/// in ay-dpll E-matching or the pipeline's two-phase solve.
#[test]
#[timeout(30000)]
fn test_fn_once_law_direct_pipeline_order() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Step 1: Encode and assert requires (postcondition(f, x, result))
    let post_call = method_call(var("f"), "postcondition", vec![var("x"), var("result")]);
    let post_term = encoder
        .encode_pure(&post_call)
        .expect("encode postcondition");
    encoder.assert_term(post_term);

    // Step 2: Encode the negated ensure (NOT postcondition_once(f, x, result))
    // This declares the postcondition_once UF
    let once_call = method_call(
        var("f"),
        "postcondition_once",
        vec![var("x"), var("result")],
    );
    let once_term = encoder
        .encode_pure(&once_call)
        .expect("encode postcondition_once");

    // Step 3: Assert fn closure laws (fn_once law connects post to once)
    encoder.assert_fn_closure_laws();

    // Step 4: Assert negated ensure
    let neg_once = encoder.solver.not(once_term);
    encoder.assert_term(neg_once);

    // Step 5: Check SAT
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fn_once law (direct pipeline order): postcondition + law + NOT postcondition_once should be UNSAT: {result:?}"
    );
}
