// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `has_closure_postcondition_*_symbols` demand guards (#1998).
//!
//! These three `pub(crate)` methods on `AYEncoder` scan `decls.logic_funcs`
//! for closure-trait UF symbol name prefixes and gate axiom emission in
//! `assert_standard_axioms` (#1997). Without direct tests, a regression
//! (e.g., wrong prefix check or missing exclusion) would silently emit
//! unnecessary axioms or skip required ones — both causing solver regressions.
//!
//! Coverage:
//! - `has_closure_postcondition_once_symbols`: prefix `closure_postcondition_once_`
//! - `has_closure_postcondition_fn_symbols`: prefix `closure_postcondition_` excluding `_once_` and `_mut_`
//! - `has_closure_postcondition_mut_symbols`: prefix `closure_postcondition_mut_`

use ntest::timeout;

use super::*;

/// Helper: declare a UF in the encoder's `logic_funcs` registry with the given
/// SMT name. The UF has a trivial `() -> Bool` signature — we only care about
/// the name prefix for these demand-guard tests.
fn register_logic_func(encoder: &mut AYEncoder, smt_name: &str) {
    let decl = encoder.solver.declare_fun(smt_name, &[], Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name.to_string(), decl);
}

// ── Empty encoder baseline ──────────────────────────────────────────

#[test]
#[timeout(5000)]
fn test_empty_encoder_has_no_once_symbols() {
    let encoder = AYEncoder::new_with_quantifiers();
    assert!(!encoder.has_closure_postcondition_once_symbols());
}

#[test]
#[timeout(5000)]
fn test_empty_encoder_has_no_fn_symbols() {
    let encoder = AYEncoder::new_with_quantifiers();
    assert!(!encoder.has_closure_postcondition_fn_symbols());
}

#[test]
#[timeout(5000)]
fn test_empty_encoder_has_no_mut_symbols() {
    let encoder = AYEncoder::new_with_quantifiers();
    assert!(!encoder.has_closure_postcondition_mut_symbols());
}

// ── Single-category presence ────────────────────────────────────────

#[test]
#[timeout(5000)]
fn test_once_symbol_detected() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_once_ClosureEnv42");
    assert!(encoder.has_closure_postcondition_once_symbols());
}

#[test]
#[timeout(5000)]
fn test_once_symbol_does_not_trigger_fn_guard() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_once_ClosureEnv42");
    assert!(
        !encoder.has_closure_postcondition_fn_symbols(),
        "postcondition_once should be excluded from the Fn-trait guard"
    );
}

#[test]
#[timeout(5000)]
fn test_once_symbol_does_not_trigger_mut_guard() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_once_ClosureEnv42");
    assert!(
        !encoder.has_closure_postcondition_mut_symbols(),
        "postcondition_once should not match postcondition_mut prefix"
    );
}

#[test]
#[timeout(5000)]
fn test_mut_symbol_detected() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_mut_ClosureEnv7");
    assert!(encoder.has_closure_postcondition_mut_symbols());
}

#[test]
#[timeout(5000)]
fn test_mut_symbol_does_not_trigger_fn_guard() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_mut_ClosureEnv7");
    assert!(
        !encoder.has_closure_postcondition_fn_symbols(),
        "postcondition_mut should be excluded from the Fn-trait guard"
    );
}

#[test]
#[timeout(5000)]
fn test_mut_symbol_does_not_trigger_once_guard() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_mut_ClosureEnv7");
    assert!(
        !encoder.has_closure_postcondition_once_symbols(),
        "postcondition_mut should not match postcondition_once prefix"
    );
}

#[test]
#[timeout(5000)]
fn test_fn_symbol_detected() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    // Fn-trait postconditions use `closure_postcondition_` without `once_` or `mut_`
    register_logic_func(&mut encoder, "closure_postcondition_ClosureEnv99");
    assert!(encoder.has_closure_postcondition_fn_symbols());
}

#[test]
#[timeout(5000)]
fn test_fn_symbol_does_not_trigger_once_guard() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_ClosureEnv99");
    assert!(
        !encoder.has_closure_postcondition_once_symbols(),
        "plain closure_postcondition_ should not match once prefix"
    );
}

#[test]
#[timeout(5000)]
fn test_fn_symbol_does_not_trigger_mut_guard() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_ClosureEnv99");
    assert!(
        !encoder.has_closure_postcondition_mut_symbols(),
        "plain closure_postcondition_ should not match mut prefix"
    );
}

// ── All three categories present ────────────────────────────────────

#[test]
#[timeout(5000)]
fn test_all_three_categories_present() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_once_A");
    register_logic_func(&mut encoder, "closure_postcondition_B");
    register_logic_func(&mut encoder, "closure_postcondition_mut_C");

    assert!(encoder.has_closure_postcondition_once_symbols());
    assert!(encoder.has_closure_postcondition_fn_symbols());
    assert!(encoder.has_closure_postcondition_mut_symbols());
}

// ── Edge cases ──────────────────────────────────────────────────────

/// Unrelated logic funcs should not trigger any guard.
#[test]
#[timeout(5000)]
fn test_unrelated_logic_func_does_not_trigger_any_guard() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "method_view_1_i");
    register_logic_func(&mut encoder, "closure_precondition_Env0");
    register_logic_func(&mut encoder, "postcondition_not_closure");

    assert!(!encoder.has_closure_postcondition_once_symbols());
    assert!(!encoder.has_closure_postcondition_fn_symbols());
    assert!(!encoder.has_closure_postcondition_mut_symbols());
}

/// Multiple once symbols — guard should still fire.
#[test]
#[timeout(5000)]
fn test_multiple_once_symbols() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_once_Env0");
    register_logic_func(&mut encoder, "closure_postcondition_once_Env1");
    register_logic_func(&mut encoder, "closure_postcondition_once_Env2");

    assert!(encoder.has_closure_postcondition_once_symbols());
    assert!(!encoder.has_closure_postcondition_fn_symbols());
    assert!(!encoder.has_closure_postcondition_mut_symbols());
}

/// `closure_postcondition_mut_once_Env` is a mut symbol (starts with
/// `closure_postcondition_mut_`), not a once symbol.
#[test]
#[timeout(5000)]
fn test_mut_once_hybrid_name_classified_as_mut() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_logic_func(&mut encoder, "closure_postcondition_mut_once_Env0");

    assert!(
        encoder.has_closure_postcondition_mut_symbols(),
        "should match mut prefix"
    );
    assert!(
        !encoder.has_closure_postcondition_once_symbols(),
        "should NOT match once prefix (mut_ prefix is longer and matches first)"
    );
    // The fn guard excludes both _once_ and _mut_ names
    assert!(
        !encoder.has_closure_postcondition_fn_symbols(),
        "should be excluded from fn guard due to mut prefix"
    );
}
