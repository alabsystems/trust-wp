// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for logic function registration edge cases in `logic_fn/mod.rs`.
//!
//! Complements existing tests in `tests/logic_fn/` by covering:
//! - Mode override length mismatch (fail-closed guard)
//! - Zero-param lemma spec axiom emission
//! - Opaque function: spec axiom without defining axiom
//! - Recursive limited encoding declaration
//! - Idempotent registration
//!
//! Part of #2514 (Tier 2 coverage gap: logic_fn/mod.rs, 855 LOC).

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::{
    formula::{intern_sort_name, ExprSort, PureExpr},
    logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind, LogicFnDef, LogicMode},
};

use super::super::{super::*, helpers::*};

// ── Mode override length mismatch ───────────────────────────────────

/// `register_logic_fns_with_modes` rejects mismatched override length.
#[test]
#[timeout(30000)]
fn mode_override_length_mismatch_rejected() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fn1 = LogicFnDef::new(
        "fn1".to_string(),
        "test::fn1".to_string(),
        vec!["x".to_string()],
        int(0),
    );
    let fn2 = LogicFnDef::new(
        "fn2".to_string(),
        "test::fn2".to_string(),
        vec!["x".to_string()],
        int(0),
    );

    // 2 functions but 1 mode override
    let result = encoder.register_logic_fns_with_modes(&[fn1, fn2], Some(&[LogicMode::Open]));
    assert!(
        result.is_err(),
        "mismatched mode override length should fail"
    );
}

/// `register_logic_fns_with_modes` with None uses default modes.
#[test]
#[timeout(30000)]
fn mode_override_none_uses_default() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let func = LogicFnDef::new(
        "nonefn".to_string(),
        "test::nonefn".to_string(),
        vec!["x".to_string()],
        int(0),
    )
    .with_mode(LogicMode::Open);

    let result = encoder.register_logic_fns_with_modes(&[func], None);
    assert!(
        result.is_ok(),
        "None mode overrides should use default modes"
    );
}

// ── Zero-param lemma spec axiom ─────────────────────────────────────

/// A zero-param lemma with #[ensures] asserts the ensures directly (no forall).
#[test]
#[timeout(30000)]
fn lemma_ensures_asserted_directly() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Lemma: fn truth() ensures(true)
    let mut lemma = LogicFnDef::new(
        "truth".to_string(),
        "test::truth".to_string(),
        vec![],          // zero params
        bool_expr(true), // body
    )
    .with_mode(LogicMode::Open);
    lemma.set_ensures(vec![bool_expr(true)]);

    encoder
        .register_logic_fn(&lemma)
        .expect("lemma registration should succeed");
}

/// A parameterized function with #[ensures] wraps the ensures in a forall.
#[test]
#[timeout(30000)]
fn function_ensures_wrapped_in_forall() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // fn ident(x: Int) -> Int { x } ensures(result == x)
    let mut func = LogicFnDef::new(
        "identfn".to_string(),
        "test::identfn".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);
    func.set_ensures(vec![eq(var("result"), var("x"))]);

    encoder
        .register_logic_fn(&func)
        .expect("parameterized function registration should succeed");

    // Verify: ident(5) should equal 5 (defining axiom)
    let call = logic_fn_call("identfn", vec![int(5)]);
    let call_term = encoder.encode_pure(&call).expect("encode identfn(5)");
    let five = encoder.solver.int_const(5);
    let eq_term = encoder.solver.eq(call_term, five);
    let neq = encoder.solver.not(eq_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "identfn(5) != 5 should be Unsat (defining axiom: identfn(x) = x)"
    );
}

// ── Opaque function with ensures ────────────────────────────────────

/// An opaque function suppresses the defining axiom but emits spec axioms.
#[test]
#[timeout(30000)]
fn opaque_fn_emits_spec_axiom_not_defining() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // fn secretfn(x: Int) -> Int { x + 1 } ensures(result > x), opaque
    let mut func = LogicFnDef::new(
        "secretfn".to_string(),
        "test::secretfn".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Default); // opaque by default
    func.set_ensures(vec![gt(var("result"), var("x"))]);

    encoder
        .register_logic_fn(&func)
        .expect("opaque function registration should succeed");

    // The spec axiom says result > x. Check: secretfn(0) > 0.
    let call = logic_fn_call("secretfn", vec![int(0)]);
    let call_term = encoder.encode_pure(&call).expect("encode secretfn(0)");
    let zero = encoder.solver.int_const(0);
    let gt_term = encoder.solver.gt(call_term, zero);
    let not_gt = encoder.solver.not(gt_term);
    encoder.assert_term(not_gt);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(secretfn(0) > 0) should be Unsat from spec axiom"
    );
}

/// An opaque function's defining axiom (body) is NOT available.
#[test]
#[timeout(30000)]
fn opaque_fn_body_not_available() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // fn opaquefn(x: Int) -> Int { x + 1 }, opaque, ensures(result > x)
    let mut func = LogicFnDef::new(
        "opaquefn".to_string(),
        "test::opaquefn".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Default);
    func.set_ensures(vec![gt(var("result"), var("x"))]);

    encoder
        .register_logic_fn(&func)
        .expect("opaque fn registration");

    // Try to derive opaquefn(0) == 1 — should NOT be derivable
    let call = logic_fn_call("opaquefn", vec![int(0)]);
    let call_term = encoder.encode_pure(&call).expect("encode opaquefn(0)");
    let one = encoder.solver.int_const(1);
    let eq_term = encoder.solver.eq(call_term, one);
    let neq = encoder.solver.not(eq_term);
    encoder.assert_term(neq);
    assert!(
        !matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "opaquefn(0) != 1 should be Sat (defining axiom suppressed)"
    );
}

/// Datatype parameter sorts installed for logic-body encoding must be restored
/// afterward so they do not leak into later encoder state. (#2257)
#[test]
#[timeout(30000)]
fn open_logic_fn_restores_datatype_param_var_sorts() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let zero_sort = ExprSort::Datatype(intern_sort_name("Zero"));
    let adt_decls = std::collections::HashMap::from([(
        "Zero".to_string(),
        AdtDecl::new(
            "Zero".to_string(),
            "Zero".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Zero".to_string(),
                "Zero".to_string(),
                vec![AdtFieldDecl::new("0".to_string(), ExprSort::Int)],
            )],
        ),
    )]);
    encoder.register_adt_decls(&adt_decls);

    let func = LogicFnDef::new(
        "keep_zero".to_string(),
        "test::keep_zero".to_string(),
        vec!["self".to_string()],
        bool_expr(true),
    )
    .with_param_sorts(vec![Some(zero_sort)])
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&func)
        .expect("open datatype-param logic fn should register");

    assert!(
        encoder.var_sort("self").is_none(),
        "datatype param var_sort should be restored after registration"
    );
}

/// Opaque/spec axioms must encode datatype field projections against the local
/// parameter/result sorts and restore that temporary sort state afterward. (#2257)
#[test]
#[timeout(30000)]
fn opaque_spec_axiom_uses_local_datatype_param_and_result_sorts() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let zero_sort_expr = ExprSort::Datatype(intern_sort_name("Zero"));
    let adt_decls = std::collections::HashMap::from([(
        "Zero".to_string(),
        AdtDecl::new(
            "Zero".to_string(),
            "Zero".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Zero".to_string(),
                "Zero".to_string(),
                vec![
                    AdtFieldDecl::new("0".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("1".to_string(), ExprSort::Int),
                ],
            )],
        ),
    )]);
    encoder.register_adt_decls(&adt_decls);

    let registered_zero_sort = encoder.sort_from_expr_sort(zero_sort_expr.clone());
    let ay_dpll::api::Sort::Datatype(registered_zero_dt) = registered_zero_sort.clone() else {
        panic!("registered Zero sort should be a native datatype");
    };
    let (field0_selector, field0_sort) = encoder
        .native_positional_field_selector(&registered_zero_sort, 0)
        .expect("Zero field 0 selector should resolve");

    let mut func = LogicFnDef::new(
        "project_zero".to_string(),
        "test::project_zero".to_string(),
        vec!["arg".to_string()],
        int(0),
    )
    .with_param_sorts(vec![Some(zero_sort_expr.clone())])
    .with_return_sort(Some(zero_sort_expr))
    .with_mode(LogicMode::Default);
    func.set_ensures(vec![PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("result".to_string(), None)],
        }),
        trust_wp_core::formula::BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("arg".to_string(), None)],
        }),
    )]);

    encoder
        .register_logic_fn(&func)
        .expect("opaque datatype-returning fn should emit spec axiom");

    assert!(
        encoder.var_sort("arg").is_none(),
        "spec-axiom param var_sort should be restored after registration"
    );
    assert!(
        encoder.var_sort("result").is_none(),
        "spec-axiom result var_sort should be restored after registration"
    );

    let x = encoder.solver.declare_const(
        "x_project_zero",
        ay_dpll::api::Sort::Datatype(registered_zero_dt),
    );
    encoder.rebind_var("x", x, registered_zero_sort.clone());

    let call = logic_fn_call("project_zero", vec![var("x")]);
    let call_term = encoder
        .encode_pure(&call)
        .expect("datatype-returning opaque call should encode");
    let call_field0 = encoder
        .solver
        .try_datatype_selector(&field0_selector, call_term, field0_sort)
        .expect("call field selector should apply");
    let x_field0 = encoder
        .solver
        .try_datatype_selector(&field0_selector, x, ay_dpll::api::Sort::Int)
        .expect("arg field selector should apply");
    let eq_term = encoder.solver.eq(call_field0, x_field0);
    let neq = encoder.solver.not(eq_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "opaque spec axiom should preserve datatype field projection equality"
    );
}

// ── Recursive function registration (no dead _lim declarations) ─────

/// Recursive functions no longer get a dead `f_lim` declaration (#2646).
/// The HKMS12 limited encoding was removed because `f_lim` was never
/// referenced in spec axioms, call encoding, or VCs. trust-wp handles
/// recursive functions via ground evaluation and one-step unfolding.
#[test]
#[timeout(30000)]
fn recursive_fn_no_lim_declaration() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // fn recfn(n: Int) -> Int { if n <= 0 { 1 } else { recfn(n-1) } }
    let mut func = LogicFnDef::new(
        "recfn".to_string(),
        "test::recfn".to_string(),
        vec!["n".to_string()],
        ite(
            le(var("n"), int(0)),
            int(1),
            logic_fn_call("recfn", vec![add(var("n"), int(-1))]),
        ),
    )
    .with_mode(LogicMode::Open);
    func.set_is_recursive(true);

    encoder
        .register_logic_fn(&func)
        .expect("recursive function registration");

    // The defining axiom for the function itself should exist
    assert!(
        encoder.decls().has_logic_func("logic_recfn"),
        "recursive function should be declared"
    );

    // No _lim declaration — the dead HKMS12 encoding was removed (#2646)
    assert!(
        !encoder.decls().has_logic_func("logic_recfn_lim"),
        "recursive function should NOT get a dead _lim declaration"
    );
}

/// Non-recursive functions do NOT get a `_lim` declaration.
#[test]
#[timeout(30000)]
fn non_recursive_fn_no_lim_declaration() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let func = LogicFnDef::new(
        "normalfn".to_string(),
        "test::normalfn".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&func)
        .expect("non-recursive registration");

    assert!(
        !encoder.decls().has_logic_func("logic_normalfn_lim"),
        "non-recursive function should NOT get a _lim declaration"
    );
}

// ── Return sort hint preseeding ─────────────────────────────────────

/// Bool return sort is preseeded and used for signature declaration.
#[test]
#[timeout(30000)]
fn bool_return_sort_produces_bool_declaration() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let func = LogicFnDef::new(
        "boolpred".to_string(),
        "test::boolpred".to_string(),
        vec!["x".to_string()],
        bool_expr(true),
    )
    .with_return_sort(Some(ExprSort::Bool))
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&func)
        .expect("Bool return sort registration");

    // The declared function should have Bool return sort (via pub(crate) decls())
    let decl = encoder.decls().get_logic_func("logic_boolpred");
    assert!(decl.is_some(), "function should be declared");
    assert_eq!(
        decl.unwrap().range(),
        &ay_dpll::api::Sort::Bool,
        "Bool return sort should be reflected in the declaration"
    );
}

// ── Idempotent registration ─────────────────────────────────────────

/// Double registration is a no-op (idempotent).
#[test]
#[timeout(30000)]
fn double_registration_idempotent() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let func = LogicFnDef::new(
        "idemfn".to_string(),
        "test::idemfn".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&func)
        .expect("first registration");
    encoder
        .register_logic_fn(&func)
        .expect("second registration should be no-op");

    // Verify the function still works correctly
    let call = logic_fn_call("idemfn", vec![int(7)]);
    let call_term = encoder.encode_pure(&call).expect("encode idemfn(7)");
    let seven = encoder.solver.int_const(7);
    let eq_term = encoder.solver.eq(call_term, seven);
    let neq = encoder.solver.not(eq_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "idemfn(7) != 7 should be Unsat after double registration"
    );
}

// ── Empty function list ─────────────────────────────────────────────

/// Registering zero functions is a no-op.
#[test]
#[timeout(30000)]
fn register_empty_function_list() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let result = encoder.register_logic_fns_with_modes(&[], None);
    assert!(result.is_ok(), "empty function list should succeed");

    let result = encoder.register_logic_fns_with_modes(&[], Some(&[]));
    assert!(
        result.is_ok(),
        "empty list with empty overrides should succeed"
    );
}
