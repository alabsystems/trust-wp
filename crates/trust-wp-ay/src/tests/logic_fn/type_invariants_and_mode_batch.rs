// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::{
    formula::ExprSort,
    logic::{LogicFnDef, LogicMode},
};

use super::*;

/// Test that type invariant bodies are registered through verify_function (#645).
///
/// Models a NonZeroU32-like type where `invariant(self) ↔ self > 0`.
/// The constructor `new(n)` requires `n > 0` and returns `result = n`.
/// Without the invariant body axiom, `result.invariant()` is unconstrained.
/// With the axiom, `invariant(result) = (result > 0)` connects to the
/// precondition, and the proof obligation is satisfiable.
#[test]
#[timeout(30000)]
fn test_verify_function_with_type_invariant_axiom() {
    use trust_wp_core::logic::type_invariant_method_name;

    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // invariant(self) = self > 0
    let invariant_body = gt(var("self"), int(0));

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None, // Int
        body: invariant_body,
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: n > 0
    let requires = vec![gt(var("n"), int(0))];

    // ensures: result.__trust_wp_invariant_NonZero()
    let ensures = vec![method_call(
        var("result"),
        &type_invariant_method_name("NonZero"),
        vec![],
    )];

    // body: result = n
    let return_expr = var("n");

    // WITH type invariant axiom: should verify
    // invariant(result) = (result > 0), and result = n where n > 0
    let result_with = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&return_expr))
            .type_invariants(Some(std::slice::from_ref(&inv_def))),
    );
    assert!(
        matches!(result_with, Ok(VerificationResult::Verified(_))),
        "With invariant body axiom, constructor should verify: {result_with:?}"
    );

    // WITHOUT type invariant axiom: should not verify
    // invariant(result) is unconstrained UF — solver finds counterexample
    // where invariant(result) is set to false
    let result_without = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    );
    assert!(
        crate::tests::rejected_ok(&result_without),
        "Without invariant body axiom, should produce Failed (invariant() is \
         uninterpreted UF, solver finds counterexample): {result_without:?}"
    );
}

/// Test that multiple type invariants can be registered simultaneously.
#[test]
#[timeout(30000)]
fn test_verify_function_with_multiple_type_invariants() {
    use trust_wp_core::logic::type_invariant_method_name;

    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // inv1: invariant(self) = self > 0 (NonZero-like)
    let inv1 = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // Second identical def should be deduplicated (same symbol)
    let inv2 = inv1.clone();

    // requires: x > 0
    let requires = vec![gt(var("x"), int(0))];

    // ensures: result.__trust_wp_invariant_NonZero()
    let ensures = vec![method_call(
        var("result"),
        &type_invariant_method_name("NonZero"),
        vec![],
    )];

    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv1, inv2])),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Multiple invariant defs (deduplicated) should verify: {result:?}"
    );
}

/// Regression test for #666: distinct invariant-bearing types with the same
/// SMT sort must not collide on one shared invariant symbol.
#[test]
#[timeout(30000)]
fn test_verify_function_with_distinct_type_invariant_symbols() {
    use trust_wp_core::logic::type_invariant_method_name;

    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let non_zero = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };
    let small_num = trust_wp_core::type_invariant_def! {
        type_name: "SmallNum".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: lt(var("self"), int(100)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let requires = vec![gt(var("x"), int(0)), lt(var("x"), int(100))];

    let ensures = vec![
        method_call(
            var("result"),
            &type_invariant_method_name("NonZero"),
            vec![],
        ),
        method_call(
            var("result"),
            &type_invariant_method_name("SmallNum"),
            vec![],
        ),
    ];

    let body = var("x");
    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .type_invariants(Some(&[non_zero, small_num])),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Distinct invariant symbols should verify: {result:?}"
    );
}

// --- Algorithm audit: register_logic_fns_with_modes boundary tests (#696) ---

/// register_logic_fns_with_modes should register all functions when mode
/// overrides have the same length as logic_fns.
#[test]
#[timeout(30000)]
fn test_register_logic_fns_with_modes_matching_length() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fns = vec![
        LogicFnDef::new(
            "f".to_string(),
            "crate::f".to_string(),
            vec!["x".to_string()],
            var("x"),
        )
        .with_mode(LogicMode::Open),
        LogicFnDef::new(
            "g".to_string(),
            "crate::g".to_string(),
            vec!["x".to_string()],
            var("x"),
        )
        .with_mode(LogicMode::Open),
    ];

    let modes = vec![LogicMode::Open, LogicMode::Open];
    encoder
        .register_logic_fns_with_modes(&logic_fns, Some(&modes))
        .expect("register_logic_fns_with_modes should succeed with matching lengths");
    // Both should be registered
    assert!(
        encoder.decls().has_logic_func("logic_f"),
        "f should be registered"
    );
    assert!(
        encoder.decls().has_logic_func("logic_g"),
        "g should be registered"
    );
}

/// register_logic_fns_with_modes with None mode_overrides should register
/// all functions using their default modes.
#[test]
#[timeout(30000)]
fn test_register_logic_fns_with_modes_none_uses_defaults() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fns = vec![LogicFnDef::new(
        "h".to_string(),
        "crate::h".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open)];

    encoder
        .register_logic_fns_with_modes(&logic_fns, None)
        .expect("register_logic_fns_with_modes with None should use defaults");
    assert!(
        encoder.decls().has_logic_func("logic_h"),
        "h should be registered with default mode"
    );
}

/// Algorithm audit: empty logic_fns slice should be a no-op.
#[test]
#[timeout(30000)]
fn test_register_logic_fns_with_modes_empty() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .register_logic_fns_with_modes(&[], Some(&[]))
        .expect("register_logic_fns_with_modes with empty slices should succeed");
}

/// `prescan_and_register_logic_fns` should carry Bool return-sort evidence from
/// `requires` formulas into later declarations in the same batch. Without the
/// prescan, `passthrough()` would default to Int because its body is only the
/// call `predicate()`, which has not been declared yet. (#2034)
#[test]
#[timeout(30000)]
fn test_prescan_and_register_logic_fns_requires_seed_bool_passthrough() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let mut requires_seed = LogicFnDef::new(
        "requires_seed".to_string(),
        "crate::requires_seed".to_string(),
        vec![],
        int(0),
    )
    .with_mode(LogicMode::Open);
    requires_seed.set_requires(vec![logic_fn_call("predicate", vec![])]);

    let passthrough = LogicFnDef::new(
        "passthrough".to_string(),
        "crate::passthrough".to_string(),
        vec![],
        logic_fn_call("predicate", vec![]),
    )
    .with_mode(LogicMode::Open);

    let predicate = LogicFnDef::new(
        "predicate".to_string(),
        "crate::predicate".to_string(),
        vec![],
        bool_expr(true),
    )
    .with_mode(LogicMode::Open);

    encoder
        .prescan_and_register_logic_fns(&[requires_seed, passthrough, predicate], None)
        .expect("prescan should seed Bool hints from requires formulas");

    let passthrough_call = logic_fn_call("passthrough", vec![]);
    assert_eq!(
        encoder.infer_expr_sort_with_context(&passthrough_call, None),
        Sort::Bool,
        "requires prescan should give passthrough() a Bool return sort"
    );

    let call_term = encoder
        .encode_pure(&passthrough_call)
        .expect("Bool passthrough call should encode after requires prescan");
    let true_term = encoder.solver.bool_const(true);
    let eq_true = encoder.solver.eq(call_term, true_term);
    let neq_true = encoder.solver.not(eq_true);
    encoder.assert_term(neq_true);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "predicate() = true and passthrough() = predicate() should force \
         passthrough() == true"
    );
}

/// `prescan_and_register_logic_fns` must collect Bool-returning logic-function
/// hints from `ensures` while leaving the local `result` binding out of the
/// shared sort-hint table. (#994, #2034)
#[test]
#[timeout(30000)]
fn test_prescan_and_register_logic_fns_ensures_seed_bool_passthrough_without_result_leak() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let mut ensures_seed = LogicFnDef::new(
        "ensures_seed".to_string(),
        "crate::ensures_seed".to_string(),
        vec![],
        bool_expr(true),
    )
    .with_mode(LogicMode::Open)
    .with_return_sort(Some(ExprSort::Bool));
    ensures_seed.set_ensures(vec![logic_fn_call("predicate", vec![]), var("result")]);

    let passthrough = LogicFnDef::new(
        "passthrough".to_string(),
        "crate::passthrough".to_string(),
        vec![],
        logic_fn_call("predicate", vec![]),
    )
    .with_mode(LogicMode::Open);

    let predicate = LogicFnDef::new(
        "predicate".to_string(),
        "crate::predicate".to_string(),
        vec![],
        bool_expr(true),
    )
    .with_mode(LogicMode::Open);

    encoder
        .prescan_and_register_logic_fns(&[ensures_seed, passthrough, predicate], None)
        .expect("prescan should seed Bool fn hints from ensures clauses");

    assert_eq!(
        encoder
            .sort_resolver_for_test()
            .get_sort_hint("logic_predicate"),
        Some(&ExprSort::Bool),
        "ensures prescan should keep the Bool hint for predicate()"
    );
    assert_eq!(
        encoder.sort_resolver_for_test().get_sort_hint("result"),
        None,
        "logic-fn ensures should not leak local result Bool hints globally"
    );

    let passthrough_call = logic_fn_call("passthrough", vec![]);
    assert_eq!(
        encoder.infer_expr_sort_with_context(&passthrough_call, None),
        Sort::Bool,
        "ensures prescan should give passthrough() a Bool return sort"
    );

    let call_term = encoder
        .encode_pure(&passthrough_call)
        .expect("Bool passthrough call should encode after ensures prescan");
    let true_term = encoder.solver.bool_const(true);
    let eq_true = encoder.solver.eq(call_term, true_term);
    let neq_true = encoder.solver.not(eq_true);
    encoder.assert_term(neq_true);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "predicate() = true and passthrough() = predicate() should force \
         passthrough() == true"
    );
}

/// Diagnostic: test that a type invariant ground-pool axiom works at the
/// encoder level, bypassing the full verification pipeline. Non-trivial type
/// invariants are not asserted as global quantified axioms; observed calls must
/// flow through the encoder so the ground pool can flush the defining instance.
#[test]
#[timeout(30000)]
fn test_type_invariant_axiom_fires_at_encoder_level() {
    use ay_dpll::api::Sort;
    use trust_wp_core::logic::type_invariant_method_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register type invariant: inv(self) ↔ self > 0
    let inv_body = gt(var("self"), int(0));
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: inv_body,
        is_newtype: true,
        element_invariant_method: None,
    };

    encoder.register_sort_hints(std::slice::from_ref(inv_def.body()));
    encoder.register_formula_sort_hints(std::slice::from_ref(inv_def.body()));
    encoder
        .register_type_invariant(
            inv_def.type_name(),
            inv_def.self_param(),
            Sort::Int,
            inv_def.body(),
        )
        .expect("register_type_invariant should succeed");

    // Declare variables
    let n = encoder.get_or_declare_var("n", Sort::Int).unwrap();
    let result = encoder.get_or_declare_var("result", Sort::Int).unwrap();

    // Assert: n > 0
    let zero = encoder.solver.int_const(0);
    let n_gt_0 = encoder.solver.gt(n, zero);
    encoder.assert_term(n_gt_0);

    // Assert: result = n
    let result_eq_n = encoder.solver.eq(result, n);
    encoder.assert_term(result_eq_n);

    // Assert: NOT inv(result) through the encoder route. Direct solver UF
    // application would bypass ground-pool observation for the invariant call.
    let method_name = type_invariant_method_name("NonZero");
    let inv_result = encoder
        .encode_pure(&method_call(var("result"), &method_name, vec![]))
        .expect("type invariant call should encode");
    let not_inv_result = encoder.solver.not(inv_result);
    encoder.assert_term(not_inv_result);

    // Should be UNSAT: inv(result) = (result > 0), result = n, n > 0
    // via the ground-pool instance inv(result) <=> result > 0, contradicting
    // NOT inv(result).
    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, SolveResult::Unsat(_)),
        "Type invariant axiom should fire via E-matching: got {sat_result:?}"
    );
}

/// Diagnostic: test that a type invariant ground-pool axiom fires through push/pop scopes,
/// mimicking the pipeline's scope nesting. The axiom is in the base scope, and
/// the negated postcondition is in a nested scope. This isolates whether
/// scoped ground-pool flushing works across push/pop boundaries.
#[test]
#[timeout(30000)]
fn test_type_invariant_axiom_fires_through_push_pop_scopes() {
    use ay_dpll::api::Sort;
    use trust_wp_core::logic::type_invariant_method_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register type invariant in base scope: inv(self) ↔ self > 0
    let inv_body = gt(var("self"), int(0));
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: inv_body,
        is_newtype: true,
        element_invariant_method: None,
    };

    encoder.register_sort_hints(std::slice::from_ref(inv_def.body()));
    encoder.register_formula_sort_hints(std::slice::from_ref(inv_def.body()));
    encoder
        .register_type_invariant(
            inv_def.type_name(),
            inv_def.self_param(),
            Sort::Int,
            inv_def.body(),
        )
        .expect("register_type_invariant should succeed");

    // Declare variables and assert preconditions in base scope
    let n = encoder.get_or_declare_var("n", Sort::Int).unwrap();
    let result = encoder.get_or_declare_var("result", Sort::Int).unwrap();

    let zero = encoder.solver.int_const(0);
    let n_gt_0 = encoder.solver.gt(n, zero);
    encoder.assert_term(n_gt_0);

    let result_eq_n = encoder.solver.eq(result, n);
    encoder.assert_term(result_eq_n);

    // Push slice scope (mimicking pipeline.rs:216)
    encoder.push_scope().unwrap();

    // Push Phase 1 scope (mimicking solver_tail.rs:102)
    encoder.push_scope().unwrap();

    // Assert: NOT inv(result) in nested scope through the encoder route so
    // ground-pool flushing sees the scoped invariant application.
    let method_name = type_invariant_method_name("NonZero");
    let inv_result = encoder
        .encode_pure(&method_call(var("result"), &method_name, vec![]))
        .expect("type invariant call should encode");
    let not_inv_result = encoder.solver.not(inv_result);
    encoder.assert_term(not_inv_result);

    // Should be UNSAT even through nested scopes
    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, SolveResult::Unsat(_)),
        "Type invariant axiom should fire through push/pop scopes: got {sat_result:?}"
    );

    encoder.pop_scope().unwrap();
    encoder.pop_scope().unwrap();
}

/// Test that generic logic functions with TypeParam sorts resolve to Int at declaration.
///
/// Regression test for TypeParam→Int resolution: generic type parameters like `T`
/// previously resolved to `Sort::Uninterpreted("T")`, causing sort mismatches at
/// call sites where concrete `Sort::Int` arguments are passed. The mismatch triggers
/// `__apply_coerce` fresh constants that disconnect arguments from the function body,
/// and increments the DEMOTING `SortFallbackToInt` counter — turning correct
/// `Verified` results into `Unknown(Demoted)`.
///
/// The fix in `resolve_logic_param_sort` maps `ExprSort::TypeParam(_)` → `Sort::Int`
/// at declaration time, matching the universal sort convention.
///
/// ```text
/// #[logic(open)]
/// fn reflexive<T>(x: T) -> bool { x == x }
/// // call: reflexive(42) → should match Int domain, no coercion needed
/// ```
#[test]
#[timeout(30000)]
fn test_typeparam_sort_resolves_to_int_at_declaration() {
    use trust_wp_core::formula::intern_sort_name;

    use crate::encoder::unsoundness;

    let mut encoder = AYEncoder::new_with_quantifiers();

    let t_id = intern_sort_name("T");
    let logic_fn = LogicFnDef::new(
        "reflexive".to_string(),
        "test::reflexive".to_string(),
        vec!["x".to_string()],
        eq(var("x"), var("x")),
    )
    .with_param_sorts(vec![Some(ExprSort::TypeParam(t_id))])
    .with_mode(LogicMode::Open);

    let before = unsoundness::snapshot();

    encoder
        .register_logic_fn(&logic_fn)
        .expect("TypeParam logic function registration should succeed");

    // Call with Int argument — should NOT trigger __apply_coerce sort mismatch
    let call = logic_fn_call("reflexive", vec![int(42)]);
    let call_term = encoder.encode_pure(&call).expect("encode reflexive(42)");

    // reflexive(42) = (42 == 42) = true. Assert NOT true → Unsat.
    let not_call = encoder.solver.not(call_term);
    encoder.assert_term(not_call);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "reflexive(42) should be true (axiom: reflexive(x) = x == x)"
    );

    // No SortFallbackToInt should have fired
    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert!(
        !delta.contains_key(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
        "TypeParam→Int resolution should prevent SortFallbackToInt: delta = {delta:?}"
    );
}
