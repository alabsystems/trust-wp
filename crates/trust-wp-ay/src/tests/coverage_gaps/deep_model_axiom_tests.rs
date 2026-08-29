// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for deep_model identity axiom and encoding chain (#2117).
//!
//! The deep_model identity axiom asserts `forall x. deep_model(x) = x` for
//! Int-sorted receivers. Without this, `deep_model` is a pure UF and the
//! solver cannot reason about ordering relationships on deep_model outputs.
//!
//! The full encoding chain for `gt_or_le<T: Ord + DeepModel>(x: &T, y: &T)`
//! requires three layers working together:
//! 1. View identity: `x = x_view` (from `encode_view_expr`)
//! 2. Alias constraint: `x_current = x` (from `assert_by_value_alias_constraints`)
//! 3. Ground instantiation: `deep_model(x_current) = x_current`
//!
//! Together these yield `x_view = x = x_current = deep_model(x_current)`,
//! bridging the body's `x_view` to the postcondition's `deep_model(x_current)`.

use std::sync::Arc;

use ay_dpll::api::{SolveResult, Sort, Term};
use ntest::timeout;

use crate::AYEncoder;

/// Declare the `method_deep_model_1_i` UF (Int -> Int) and insert it into
/// the encoder's `logic_funcs` map, matching what `encode_int_method_uf`
/// does at runtime.
fn declare_deep_model_uf(encoder: &mut AYEncoder) {
    let name = "method_deep_model_1_i";
    let decl = encoder.solver.declare_fun(name, &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(name.to_string(), decl);
}

/// Assert the same concrete deep_model identity that `assert_deep_model_axioms`
/// emits for recorded Int ground terms, without adding the quantified
/// background axiom. SAT-side negative controls use this to avoid treating
/// solver incompleteness on quantified formulas as an acceptable result.
fn assert_deep_model_ground_identity(encoder: &mut AYEncoder, receiver: Term) {
    let dm_decl = encoder
        .decls()
        .get_logic_func("method_deep_model_1_i")
        .expect("deep_model UF should be declared")
        .clone();
    let dm_receiver = encoder.solver.apply(&dm_decl, &[receiver]);
    let eq = encoder.eq_term(dm_receiver, receiver);
    encoder.solver.assert_term(eq);
}

/// The identity axiom: `forall x. deep_model(x) = x`.
///
/// Negation: `exists x. deep_model(x) != x` — should be UNSAT.
#[test]
#[timeout(30000)]
fn deep_model_identity_holds() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    declare_deep_model_uf(&mut encoder);
    encoder.assert_deep_model_axioms();

    let dm_decl = encoder
        .decls()
        .get_logic_func("method_deep_model_1_i")
        .expect("deep_model UF should be declared")
        .clone();

    let y = encoder.solver.fresh_var("y", Sort::Int);
    let dm_y = encoder.solver.apply(&dm_decl, &[y]);
    let neq = encoder.solver.neq(dm_y, y);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "deep_model(y) != y should be UNSAT with identity axiom, got: {result:?}"
    );
}

/// Without the axiom, deep_model(x) != x is satisfiable (UF is unconstrained).
#[test]
#[timeout(30000)]
fn deep_model_unconstrained_without_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    declare_deep_model_uf(&mut encoder);

    // Do NOT call assert_deep_model_axioms

    let dm_decl = encoder
        .decls()
        .get_logic_func("method_deep_model_1_i")
        .expect("deep_model UF should be declared")
        .clone();

    let y = encoder.solver.fresh_var("y", Sort::Int);
    let dm_y = encoder.solver.apply(&dm_decl, &[y]);
    let neq = encoder.solver.neq(dm_y, y);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "deep_model(y) != y should be SAT without axiom, got: {result:?}"
    );
}

/// The axiom enables ordering transfer: deep_model(a) <= deep_model(b)
/// when a <= b. This is the core use case from ord_trait.rs gt_or_le (#2117).
#[test]
#[timeout(30000)]
fn deep_model_preserves_ordering() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    declare_deep_model_uf(&mut encoder);
    encoder.assert_deep_model_axioms();

    let dm_decl = encoder
        .decls()
        .get_logic_func("method_deep_model_1_i")
        .expect("deep_model UF should be declared")
        .clone();

    let a = encoder.solver.fresh_var("a", Sort::Int);
    let b = encoder.solver.fresh_var("b", Sort::Int);
    let dm_a = encoder.solver.apply(&dm_decl, &[a]);
    let dm_b = encoder.solver.apply(&dm_decl, &[b]);

    // Assume a >= b
    let a_ge_b = encoder.solver.ge(a, b);
    encoder.solver.assert_term(a_ge_b);

    // Negate: NOT (deep_model(b) <= deep_model(a))
    let dm_b_le_dm_a = encoder.solver.le(dm_b, dm_a);
    let not_le = encoder.solver.not(dm_b_le_dm_a);
    encoder.solver.assert_term(not_le);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "a >= b && NOT (deep_model(b) <= deep_model(a)) should be UNSAT, got: {result:?}"
    );
}

/// The axiom is not asserted when deep_model was never declared.
/// This is a no-op safety check — assert_deep_model_axioms should
/// silently return when the UF is absent.
#[test]
#[timeout(30000)]
fn deep_model_axioms_noop_without_declaration() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Do NOT declare deep_model UF
    encoder.assert_deep_model_axioms();

    // Solver should still be satisfiable (no axioms asserted)
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "empty solver should be SAT, got: {result:?}"
    );
}

/// Ground instantiation: recorded deep_model calls get direct equalities.
///
/// This tests the eager ground instantiation added in #2117 to bypass
/// ay-dpll E-matching limitations. When `encode_deep_model_uf` records
/// ground terms, `assert_deep_model_axioms` asserts `deep_model(t) = t`
/// for each, giving the solver direct equalities instead of relying on
/// quantifier instantiation.
#[test]
#[timeout(30000)]
fn deep_model_ground_instantiation_bridges_comparison() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    declare_deep_model_uf(&mut encoder);

    let dm_decl = encoder
        .decls()
        .get_logic_func("method_deep_model_1_i")
        .expect("deep_model UF should be declared")
        .clone();

    // Simulate what the encoder does: create ground terms and record them
    let x_current = encoder.solver.declare_const("x_current", Sort::Int);
    let y_current = encoder.solver.declare_const("y_current", Sort::Int);

    // Record ground applications (matching encode_deep_model_uf behavior)
    encoder
        .sort_resolver_mut_for_test()
        .record_deep_model_ground("method_deep_model_1_i".to_string(), x_current);
    encoder
        .sort_resolver_mut_for_test()
        .record_deep_model_ground("method_deep_model_1_i".to_string(), y_current);

    // Build deep_model applications
    let dm_x = encoder.solver.apply(&dm_decl, &[x_current]);
    let dm_y = encoder.solver.apply(&dm_decl, &[y_current]);

    // Simulate gt_or_le: body says result = (x_current >= y_current)
    let result = encoder.solver.declare_const("result", Sort::Bool);
    let x_ge_y = encoder.solver.ge(x_current, y_current);
    let body_eq = encoder.solver.iff(result, x_ge_y);
    encoder.solver.assert_term(body_eq);

    // Assert axioms (quantified + ground instances)
    encoder.assert_deep_model_axioms();

    // Negate postcondition: NOT(result == (dm(y) <= dm(x)))
    let dm_y_le_dm_x = encoder.solver.le(dm_y, dm_x);
    let post_eq = encoder.solver.iff(result, dm_y_le_dm_x);
    let negated = encoder.solver.not(post_eq);
    encoder.solver.assert_term(negated);

    let solve_result = encoder.check_sat();
    assert!(
        matches!(solve_result, SolveResult::Unsat(_)),
        "gt_or_le pattern should be UNSAT with ground instantiation, got: {solve_result:?}"
    );
}

/// Full encoding chain for `gt_or_le<T: Ord + DeepModel>(x: &T, y: &T)`.
///
/// Models the complete chain that the real encoder produces:
/// - Body via PartialOrd::ge spec: `result ↔ (x_view >= y_view)`
/// - View identity: `x = x_view`, `y = y_view`
/// - Alias constraint: `x_current = x`, `y_current = y`
/// - Postcondition: `result ↔ (deep_model(y_current) <= deep_model(x_current))`
/// - Ground instantiation: `deep_model(x_current) = x_current`,
///   `deep_model(y_current) = y_current`
///
/// The previous test (`deep_model_ground_instantiation_bridges_comparison`)
/// shortcircuits the view-alias chain by using `x_current` directly in the
/// body. This test validates the full 4-variable chain:
/// `x_view = x = x_current` (view identity + alias) so that body `x_view`
/// connects to postcondition `deep_model(x_current)`.
#[test]
#[timeout(30000)]
fn deep_model_full_encoding_chain_gt_or_le() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    declare_deep_model_uf(&mut encoder);

    let dm_decl = encoder
        .decls()
        .get_logic_func("method_deep_model_1_i")
        .expect("deep_model UF should be declared")
        .clone();

    // Declare the 6 SMT variables matching the real encoding:
    // x, y: bare parameters (from spec substitution Var("x"), Var("y"))
    // x_view, y_view: from View(Var("x")), View(Var("y"))
    // x_current, y_current: from Deref(Var("x")), Deref(Var("y"))
    let x = encoder.solver.declare_const("x", Sort::Int);
    let y = encoder.solver.declare_const("y", Sort::Int);
    let x_view = encoder.solver.declare_const("x_view", Sort::Int);
    let y_view = encoder.solver.declare_const("y_view", Sort::Int);
    let x_current = encoder.solver.declare_const("x_current", Sort::Int);
    let y_current = encoder.solver.declare_const("y_current", Sort::Int);

    // View identity: x = x_view, y = y_view (from encode_view_expr)
    let eq_x_xv = encoder.solver.eq(x, x_view);
    encoder.solver.assert_term(eq_x_xv);
    let eq_y_yv = encoder.solver.eq(y, y_view);
    encoder.solver.assert_term(eq_y_yv);

    // Alias constraint: x_current = x, y_current = y
    // (from assert_by_value_alias_constraints)
    let eq_xc_x = encoder.solver.eq(x_current, x);
    encoder.solver.assert_term(eq_xc_x);
    let eq_yc_y = encoder.solver.eq(y_current, y);
    encoder.solver.assert_term(eq_yc_y);

    // Body encoding from PartialOrd::ge spec: result ↔ (x_view >= y_view)
    let result = encoder.solver.declare_const("result", Sort::Bool);
    let xv_ge_yv = encoder.solver.ge(x_view, y_view);
    let body = encoder.solver.iff(result, xv_ge_yv);
    encoder.solver.assert_term(body);

    // Record ground deep_model applications and assert axioms
    encoder
        .sort_resolver_mut_for_test()
        .record_deep_model_ground("method_deep_model_1_i".to_string(), x_current);
    encoder
        .sort_resolver_mut_for_test()
        .record_deep_model_ground("method_deep_model_1_i".to_string(), y_current);
    encoder.assert_deep_model_axioms();

    // Negate postcondition: NOT(result ↔ (deep_model(y_current) <= deep_model(x_current)))
    let dm_x = encoder.solver.apply(&dm_decl, &[x_current]);
    let dm_y = encoder.solver.apply(&dm_decl, &[y_current]);
    let dm_y_le_dm_x = encoder.solver.le(dm_y, dm_x);
    let post = encoder.solver.iff(result, dm_y_le_dm_x);
    let negated = encoder.solver.not(post);
    encoder.solver.assert_term(negated);

    let solve_result = encoder.check_sat();
    assert!(
        matches!(solve_result, SolveResult::Unsat(_)),
        "gt_or_le full chain should be UNSAT: view identity + alias + ground instantiation \
         bridges x_view to deep_model(x_current), got: {solve_result:?}"
    );
}

/// Without alias constraints, the view-to-deep_model chain is broken.
///
/// Even with view identity and ground instantiation, if the alias constraint
/// `x_current = x` is missing, the proof fails because `x_view` and
/// `x_current` are disconnected SMT variables.
#[test]
#[timeout(30000)]
fn deep_model_chain_breaks_without_alias_constraint() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    declare_deep_model_uf(&mut encoder);

    let dm_decl = encoder
        .decls()
        .get_logic_func("method_deep_model_1_i")
        .expect("deep_model UF should be declared")
        .clone();

    let x = encoder.solver.declare_const("x", Sort::Int);
    let y = encoder.solver.declare_const("y", Sort::Int);
    let x_view = encoder.solver.declare_const("x_view", Sort::Int);
    let y_view = encoder.solver.declare_const("y_view", Sort::Int);
    let x_current = encoder.solver.declare_const("x_current", Sort::Int);
    let y_current = encoder.solver.declare_const("y_current", Sort::Int);

    // View identity: x = x_view, y = y_view
    let eq_x_xv = encoder.solver.eq(x, x_view);
    encoder.solver.assert_term(eq_x_xv);
    let eq_y_yv = encoder.solver.eq(y, y_view);
    encoder.solver.assert_term(eq_y_yv);

    // NO alias constraint — x_current and x are disconnected

    // Body: result ↔ (x_view >= y_view)
    let result = encoder.solver.declare_const("result", Sort::Bool);
    let xv_ge_yv = encoder.solver.ge(x_view, y_view);
    let body = encoder.solver.iff(result, xv_ge_yv);
    encoder.solver.assert_term(body);

    // Ground identities only: this negative control must stay SAT and should
    // not depend on quantified E-matching/model validation.
    assert_deep_model_ground_identity(&mut encoder, x_current);
    assert_deep_model_ground_identity(&mut encoder, y_current);

    // Negate postcondition
    let dm_x = encoder.solver.apply(&dm_decl, &[x_current]);
    let dm_y = encoder.solver.apply(&dm_decl, &[y_current]);
    let dm_y_le_dm_x = encoder.solver.le(dm_y, dm_x);
    let post = encoder.solver.iff(result, dm_y_le_dm_x);
    let negated = encoder.solver.not(post);
    encoder.solver.assert_term(negated);

    let solve_result = encoder.check_sat();
    assert!(
        matches!(solve_result, SolveResult::Sat),
        "without alias constraint, x_view and x_current are disconnected — \
         the proof should FAIL (SAT), got: {solve_result:?}"
    );
}

/// Ground instantiation only applies to Int-sorted receivers.
/// Non-Int receivers (sort tag `u<hex>`) should NOT get ground identity axioms.
#[test]
#[timeout(30000)]
fn deep_model_ground_skips_non_int_receivers() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let seq_tagged_name = "method_deep_model_1_s";
    let seq_tagged_decl = encoder
        .solver
        .declare_fun(seq_tagged_name, &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(seq_tagged_name.to_string(), seq_tagged_decl.clone());

    // Record a non-Int receiver (sort tag `s` for Seq).
    let x = encoder.solver.declare_const("x_generic", Sort::Int);
    encoder
        .sort_resolver_mut_for_test()
        .record_deep_model_ground(seq_tagged_name.to_string(), x);

    // Assert axioms — the Seq-tagged ground term should be skipped
    encoder.assert_deep_model_axioms();

    // The Int-tagged quantified axiom may constrain method_deep_model_1_i,
    // but it must not assert a ground identity for the Seq-tagged UF.
    let dm_s_x = encoder.solver.apply(&seq_tagged_decl, &[x]);
    let neq = encoder.solver.neq(dm_s_x, x);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Seq-tagged deep_model ground term must remain unconstrained, got: {result:?}"
    );
}

/// Helper: set up the common gt_or_le encoding context.
///
/// Encodes body (View(x) >= View(y)), return_expr (call_0 ↔ result),
/// and negated postcondition (result ↔ dm(*y) <= dm(*x)) using `encode_pure`.
/// Returns the encoder ready for alias constraints and axiom assertion.
fn setup_gt_or_le_encode_pure_context() -> AYEncoder {
    use trust_wp_core::formula::PureExpr;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Body: View(Var("x")) >= View(Var("y"))
    // Creates x_view, y_view, x, y and asserts view identities
    let x_view_expr = PureExpr::View(Arc::new(PureExpr::Var("x".to_string(), None)));
    let y_view_expr = PureExpr::View(Arc::new(PureExpr::Var("y".to_string(), None)));
    let x_view_term = encoder.encode_pure(&x_view_expr).unwrap();
    let y_view_term = encoder.encode_pure(&y_view_expr).unwrap();

    // Body result: call_0 ↔ (x_view >= y_view), result ↔ call_0
    let call_0 = encoder.get_or_declare_var("call_0", Sort::Bool).unwrap();
    let ge = encoder.solver.ge(x_view_term, y_view_term);
    let body_iff = encoder.solver.iff(call_0, ge);
    encoder.solver.assert_term(body_iff);

    let result = encoder.get_or_declare_var("result", Sort::Bool).unwrap();
    let result_eq = encoder.solver.iff(result, call_0);
    encoder.solver.assert_term(result_eq);

    // Postcondition: result ↔ (dm(*y) <= dm(*x)), negated
    let deep_model_of_y = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "y".to_string(),
            None,
        )))),
        method: "deep_model".to_string(),
        args: vec![],
    };
    let deep_model_of_x = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        method: "deep_model".to_string(),
        args: vec![],
    };

    let lhs_term = encoder.encode_pure(&deep_model_of_y).unwrap();
    let rhs_term = encoder.encode_pure(&deep_model_of_x).unwrap();

    let dm_y_le_dm_x = encoder.solver.le(lhs_term, rhs_term);
    let post = encoder.solver.iff(result, dm_y_le_dm_x);
    let negated_post = encoder.solver.not(post);
    encoder.solver.assert_term(negated_post);

    encoder
}

/// Helper: assert alias constraints `x_current = x` and `y_current = y`.
fn assert_xy_alias_constraints(encoder: &mut AYEncoder) {
    if let (Ok(x_current), Ok(x_var)) = (
        encoder.get_or_declare_var("x_current", Sort::Int),
        encoder.get_or_declare_var("x", Sort::Int),
    ) {
        let alias = encoder.solver.eq(x_current, x_var);
        encoder.solver.assert_term(alias);
    }
    if let (Ok(y_current), Ok(y_var)) = (
        encoder.get_or_declare_var("y_current", Sort::Int),
        encoder.get_or_declare_var("y", Sort::Int),
    ) {
        let alias = encoder.solver.eq(y_current, y_var);
        encoder.solver.assert_term(alias);
    }
}

/// Uses `encode_pure` to replicate the real encoding for `gt_or_le`.
/// With alias constraints + ground axioms, the full chain should yield UNSAT.
#[test]
#[timeout(30000)]
fn deep_model_encode_pure_path_gt_or_le() {
    let mut encoder = setup_gt_or_le_encode_pure_context();
    assert_xy_alias_constraints(&mut encoder);
    encoder.assert_deep_model_axioms();

    let solve_result = encoder.check_sat();
    assert!(
        matches!(solve_result, SolveResult::Unsat(_)),
        "gt_or_le encode_pure path should be UNSAT with alias constraints + ground axioms, \
         got: {solve_result:?}"
    );
}

/// Same as above but WITHOUT alias constraints — should be SAT.
/// This confirms the alias constraints are critical for bridging
/// `x_view` to `x_current` via `x`.
#[test]
#[timeout(30000)]
fn deep_model_encode_pure_path_gt_or_le_no_alias() {
    let mut encoder = setup_gt_or_le_encode_pure_context();
    // NO alias constraints — x_current and x are disconnected
    let x_current = encoder
        .get_or_declare_var("x_current", Sort::Int)
        .expect("x_current should be declared by deep_model(*x)");
    let y_current = encoder
        .get_or_declare_var("y_current", Sort::Int)
        .expect("y_current should be declared by deep_model(*y)");
    assert_deep_model_ground_identity(&mut encoder, x_current);
    assert_deep_model_ground_identity(&mut encoder, y_current);

    let solve_result = encoder.check_sat();
    assert!(
        matches!(solve_result, SolveResult::Sat),
        "Without alias constraints, should be SAT (chain broken), got: {solve_result:?}"
    );
}
