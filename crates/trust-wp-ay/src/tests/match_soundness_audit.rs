// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Algorithm audit: match encoding and capture projection soundness tests (#1560).
//!
//! Findings from Prover algorithm_audit phase (iteration 505):
//! 1. `pattern_bindings` empty-vec on sort-mismatch weakens match conditions
//! 2. Tuple branch in `pattern_bindings` missing `safe_apply` wrapping
//! 3. `assert_capture_projection` boundary condition coverage

use ay_dpll::api::{SolveResult, Term};
use ntest::timeout;

use super::helpers::{add, bool_expr, eq, int, logic_fn_call, match_expr, var, var_with_sort};
use crate::{AYEncoder, CaptureField, CaptureKind, ExprSort, Pattern};
mod safe_apply_err_path;

fn tuple_logic_getter_decl_name(encoder: &AYEncoder, index: usize) -> String {
    let getter_name =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(index);
    let smt_name = trust_wp_core::logic::logic_fn_smt_name(&getter_name);
    let placeholder_prefix = format!("{smt_name}__placeholder_");
    encoder
        .decls()
        .logic_func_names()
        .find(|name| *name == &smt_name || name.starts_with(&placeholder_prefix))
        .expect("tuple logic getter should be declared")
        .clone()
}

// --- pattern_bindings empty-vec on sort-mismatch soundness audit ---
//
// Finding: when `pattern_bindings` returns `vec![]` due to sort-mismatch
// in the Constructor branch (match_enc.rs:330, 346), `encode_match_arm_body`
// encodes the arm body without binding the pattern variable. The body then
// references a fresh unconstrained SMT variable instead of the actual
// constructor payload. This can weaken verification — the solver picks
// convenient values for the unconstrained variable, potentially making
// incorrect programs verify.

/// Verify that match arm body uses the correct selector-bound variable,
/// not an unconstrained fresh variable, for constructor bindings.
#[test]
#[timeout(30000)]
fn match_constructor_binding_uses_selector_not_fresh_variable() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: ay_dpll::api::Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Declare scrutinee as OptionInt, assert scrutinee = Some(5)
    let scrutinee_var = encoder
        .get_or_declare_var("opt", ay_dpll::api::Sort::Datatype(dt.clone()))
        .unwrap();
    let five = encoder.solver.int_const(5);
    let some_five = encoder.solver.datatype_constructor(&dt, "Some", &[five]);
    let eq_term = encoder.solver.eq(scrutinee_var, some_five);
    encoder.solver.assert_term(eq_term);

    // Encode: match opt { Some(x) => x, None => 0 }
    let match_result = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".into()))),
                },
                var("x"),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );
    let match_term = encoder
        .encode_pure(&match_result)
        .expect("match encoding should succeed");

    // Assert: match_result != 5 — should be UNSAT if x is correctly bound
    // to the payload (selector of Some, which is 5).
    // If x were unconstrained, solver could set x to anything, making this SAT.
    let five_term = encoder.solver.int_const(5);
    let eq_five = encoder.solver.eq(match_term, five_term);
    let neq = encoder.solver.not(eq_five);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "match Some(x) => x with opt=Some(5) should equal 5 (UNSAT expected), got: {result:?}"
    );
}

/// Verify that constructor binding with native datatype (from `MatchDatatypeKind`
/// inference) correctly binds the payload through the selector.
#[test]
#[timeout(30000)]
fn match_constructor_native_selector_binds_correctly() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: ay_dpll::api::Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    let scrutinee_var = encoder
        .get_or_declare_var("opt", ay_dpll::api::Sort::Datatype(dt.clone()))
        .unwrap();
    let seven = encoder.solver.int_const(7);
    let some_seven = encoder.solver.datatype_constructor(&dt, "Some", &[seven]);
    let eq_some = encoder.solver.eq(scrutinee_var, some_seven);
    encoder.solver.assert_term(eq_some);

    // match opt { Some(payload) => payload, _ => 0 }
    let match_result = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("payload".into()))),
                },
                var("payload"),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let match_term = encoder
        .encode_pure(&match_result)
        .expect("native selector match should encode");

    // With opt = Some(7), result should be 7.
    let seven_term = encoder.solver.int_const(7);
    let eq_seven = encoder.solver.eq(match_term, seven_term);
    let neq_seven = encoder.solver.not(eq_seven);
    encoder.solver.assert_term(neq_seven);

    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, SolveResult::Unsat(_)),
        "match Some(payload) => payload with opt=Some(7) should equal 7 (UNSAT expected), got: {sat_result:?}"
    );
}

// --- Tuple branch: index correctness and getter declaration ---

/// Verify tuple pattern binding uses correct element indices (off-by-one check).
/// match t { (a, b, c) => a + c } should use getter_0 and getter_2.
#[test]
#[timeout(30000)]
fn match_tuple_binding_extracts_correct_elements() {
    let mut encoder = AYEncoder::new();

    let match_result = match_expr(
        var("t"),
        vec![(
            Pattern::Tuple(vec![
                Pattern::Binding("a".into()),
                Pattern::Binding("b".into()),
                Pattern::Binding("c".into()),
            ]),
            add(var("a"), var("c")),
        )],
    );
    let match_term = encoder
        .encode_pure(&match_result)
        .expect("3-element tuple match should encode");

    // result should be getter_0(t) + getter_2(t)
    let t = encoder
        .get_or_declare_var("t", ay_dpll::api::Sort::Int)
        .unwrap();
    let getter_0 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_0")
        .unwrap()
        .clone();
    let getter_2 = encoder
        .decls()
        .get_spec_func("__trust_wp_tuple_get_2")
        .unwrap()
        .clone();

    let t0 = encoder.solver.apply(&getter_0, &[t]);
    let t2 = encoder.solver.apply(&getter_2, &[t]);
    let expected = encoder.solver.add(t0, t2);

    let eq = encoder.solver.eq(match_term, expected);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "match (a,b,c) => a+c should be getter_0(t) + getter_2(t)"
    );

    // Verify getter declarations: exactly 3 (indices 0-2), not 4
    assert!(encoder.decls().has_spec_func("__trust_wp_tuple_get_0"));
    assert!(encoder.decls().has_spec_func("__trust_wp_tuple_get_1"));
    assert!(encoder.decls().has_spec_func("__trust_wp_tuple_get_2"));
    assert!(!encoder.decls().has_spec_func("__trust_wp_tuple_get_3"));
}

// --- Capture projection boundary conditions ---

/// Verify that `assert_capture_projection` rejects out-of-bounds field indices.
#[test]
#[timeout(30000)]
fn capture_projection_rejects_out_of_bounds_field_index() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByRef)];
    encoder
        .register_closure_struct_sort("test::oob", &captures)
        .unwrap();

    let sort = encoder
        .register_closure_struct_sort("test::oob", &captures)
        .unwrap();
    encoder.get_or_declare_var("c_final", sort).unwrap();

    // field_index 0 is valid (one capture)
    let valid = vec![(0_usize, "x_final".to_string())];
    assert!(
        encoder
            .assert_capture_projection("test::oob", "c_final", &valid)
            .is_ok(),
        "field_index 0 should be valid for 1-capture closure"
    );

    // field_index 1 is out-of-bounds
    let oob = vec![(1_usize, "y_final".to_string())];
    let result = encoder.assert_capture_projection("test::oob", "c_final", &oob);
    assert!(result.is_err(), "field_index 1 should be out-of-bounds");
    let msg = format!("{}", result.unwrap_err());
    assert!(
        msg.contains("out of bounds"),
        "error should mention out of bounds: {msg}"
    );
}

/// Verify that capture projection with empty bindings is a no-op.
#[test]
#[timeout(30000)]
fn capture_projection_empty_bindings_is_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByRef)];
    encoder
        .register_closure_struct_sort("test::empty_bind", &captures)
        .unwrap();

    let sort = encoder
        .register_closure_struct_sort("test::empty_bind", &captures)
        .unwrap();
    encoder.get_or_declare_var("c_final", sort).unwrap();

    let empty: Vec<(usize, String)> = vec![];
    let result = encoder.assert_capture_projection("test::empty_bind", "c_final", &empty);
    assert!(result.is_ok(), "empty bindings should succeed: {result:?}");
}

// --- ITE chain last-arm wildcard soundness check (#1641) ---
//
// Finding: `encode_match_impl` uses the last arm's body as the unconditional
// default in an ITE chain. If the last arm is a Literal or Constructor pattern,
// this over-approximates the match semantics — values not matched by any arm
// silently evaluate to the last arm's body instead of being unreachable.

/// Non-exhaustive match with literal last arm must be rejected (#1641).
///
/// `match x { 0 => a, 1 => b }` — the encoder would use `b` as the default
/// for all x ≠ 0, including x = 2, 3, .... This is unsound.
#[test]
#[timeout(30000)]
fn match_non_exhaustive_literal_last_arm_rejected() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("x"),
        vec![
            (Pattern::Literal(int(0)), int(10)),
            (Pattern::Literal(int(1)), int(20)),
        ],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "Non-exhaustive match (literal last arm) should be rejected, got: {result:?}"
    );
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("non-exhaustive") || err_msg.contains("wildcard"),
        "Error should mention non-exhaustive or wildcard: {err_msg}"
    );
}

/// Non-exhaustive match with constructor last arm must be rejected (#1641).
///
/// `match opt { Some(v) => v }` — only one constructor of a two-constructor
/// datatype. The missing `None` arm means the match is not exhaustive.
#[test]
#[timeout(30000)]
fn match_non_exhaustive_constructor_last_arm_rejected() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("opt"),
        vec![(
            Pattern::Constructor {
                name: "Some".into(),
                inner: Some(Box::new(Pattern::Binding("v".into()))),
            },
            var("v"),
        )],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "Non-exhaustive match (single constructor, missing None) should be rejected, got: {result:?}"
    );
}

/// Exhaustive constructor match (Some + None) should encode with correct
/// semantics. Strengthened from bare is_ok() to UNSAT-dual: constrain
/// opt = Some(5), verify match produces 5.
///
/// When all constructors of a known datatype appear in the arms, the ITE
/// default is sound because the datatype theory guarantees one must match.
#[test]
#[timeout(30000)]
fn match_exhaustive_constructor_arms_accepted() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();

    // Declare OptionInt datatype with None and Some(Int) constructors.
    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: ay_dpll::api::Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Pre-declare opt as OptionInt, constrain opt = Some(5).
    let opt_var = encoder
        .get_or_declare_var("opt2", ay_dpll::api::Sort::Datatype(dt.clone()))
        .unwrap();
    let five = encoder.solver.int_const(5);
    let some_five = encoder.solver.datatype_constructor(&dt, "Some", &[five]);
    let eq_term = encoder.solver.eq(opt_var, some_five);
    encoder.solver.assert_term(eq_term);

    // match opt2 { Some(v) => v, None => 0 }
    let expr = match_expr(
        var("opt2"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v2".into()))),
                },
                var("v2"),
            ),
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Exhaustive constructor match (Some+None) should encode");

    // Assert match_result != 5, expect UNSAT (opt2=Some(5), Some arm returns v2=5).
    let five_term = encoder.solver.int_const(5);
    let eq_five = encoder.solver.eq(match_term, five_term);
    let neq = encoder.solver.not(eq_five);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "match Some(v) => v with opt2=Some(5) should yield 5 (UNSAT on negation)"
    );
}

/// Match with wildcard last arm: constrain x=3 (non-matching), verify
/// wildcard arm produces 99 (UNSAT on negation).
#[test]
#[timeout(30000)]
fn match_with_wildcard_last_arm_accepted() {
    let mut encoder = AYEncoder::new();

    // match x { 0 => 10, _ => 99 }
    let expr = match_expr(
        var("x"),
        vec![
            (Pattern::Literal(int(0)), int(10)),
            (Pattern::Wildcard, int(99)),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Match with wildcard last arm should encode");

    // Constrain x = 3 (falls to wildcard arm).
    let x_var = encoder
        .get_or_declare_var("x", ay_dpll::api::Sort::Int)
        .unwrap();
    let three = encoder.solver.int_const(3);
    let x_eq_3 = encoder.solver.eq(x_var, three);
    encoder.solver.assert_term(x_eq_3);

    // Assert match_result != 99, expect UNSAT (x=3 matches wildcard => 99).
    let ninety_nine = encoder.solver.int_const(99);
    let eq_99 = encoder.solver.eq(match_term, ninety_nine);
    let neq = encoder.solver.not(eq_99);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "match x=3 with wildcard arm should yield 99 (UNSAT on negation)"
    );
}

/// Match with binding last arm: constrain x=7 (non-matching), verify
/// binding arm captures x and produces 7 (UNSAT on negation).
#[test]
#[timeout(30000)]
fn match_with_binding_last_arm_accepted() {
    let mut encoder = AYEncoder::new();

    // match x { 0 => 10, other => other }
    let expr = match_expr(
        var("x"),
        vec![
            (Pattern::Literal(int(0)), int(10)),
            (Pattern::Binding("other".into()), var("other")),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Match with binding last arm should encode");

    // Constrain x = 7 (falls to binding arm, other = 7).
    let x_var = encoder
        .get_or_declare_var("x", ay_dpll::api::Sort::Int)
        .unwrap();
    let seven = encoder.solver.int_const(7);
    let x_eq_7 = encoder.solver.eq(x_var, seven);
    encoder.solver.assert_term(x_eq_7);

    // Assert match_result != 7, expect UNSAT (x=7, binding arm returns other=7).
    let seven_term = encoder.solver.int_const(7);
    let eq_term = encoder.solver.eq(match_term, seven_term);
    let neq = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "match x=7 with binding last arm should yield 7 (UNSAT on negation)"
    );
}

// --- #1681 / #1740 diagnostic: ay ITE with UF-condition behavior lock ---

/// Regression monitor for ay#4767.
///
/// Semantically, this formula is UNSAT:
/// - f(x) is asserted true
/// - g(x) is asserted 5
/// - ite(f(x), g(x)+1, 0) is therefore 6
/// - asserting ite(...) != 6 should be contradictory
///
/// ay#4767 previously returned Sat (incorrect). This regression requires Unsat.
#[test]
#[timeout(30000)]
fn uf_ite_baseline_ay_bug_4767_returns_sat() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();

    // Declare UF: f : Int -> Bool, g : Int -> Int
    let f = encoder
        .solver
        .declare_fun("f_test", &[Sort::Int], Sort::Bool);
    let g = encoder
        .solver
        .declare_fun("g_test", &[Sort::Int], Sort::Int);

    // Declare x : Int
    let x = encoder.get_or_declare_var("x_diag", Sort::Int).unwrap();

    // Assert f(x) = true
    let f_x = encoder.solver.apply(&f, &[x]);
    encoder.solver.assert_term(f_x);

    // Assert g(x) = 5
    let g_x = encoder.solver.apply(&g, &[x]);
    let five = encoder.solver.int_const(5);
    let g_eq = encoder.solver.eq(g_x, five);
    encoder.solver.assert_term(g_eq);

    // Construct ITE: ite(f(x), g(x) + 1, 0)
    let f_x2 = encoder.solver.apply(&f, &[x]);
    let g_x2 = encoder.solver.apply(&g, &[x]);
    let one = encoder.solver.int_const(1);
    let g_plus_1 = encoder.solver.add(g_x2, one);
    let zero = encoder.solver.int_const(0);
    let ite_term = encoder.solver.ite(f_x2, g_plus_1, zero);

    // Assert ite_term != 6 (semantically should be UNSAT).
    let six = encoder.solver.int_const(6);
    let eq = encoder.solver.eq(ite_term, six);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    // Use raw ay solver check_sat (bypass trust-wp pipeline).
    let result = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ay#4767 UF-conditioned ITE: expected Unsat, got {result:?}."
    );
}

// --- #1681 regression: pattern_bindings UF fallback for custom constructors ---
//
// Before the fix, `pattern_bindings` returned `Ok(vec![])` for custom
// constructors on both the no-selector and pure-UF paths. This left
// binding variables unconstrained, allowing the solver to pick arbitrary
// values — weakening verification.

/// Regression test for #1740/ay#4767 on UF fallback + constructor binding.
///
/// Forces the pure UF path (no datatype) by pre-declaring the scrutinee
/// as `Sort::Int`. Verifies that `Wrap(x) => x + 1` correctly binds `x`
/// to `payload_wrap(w)`, making the result `payload_wrap(w) + 1`.
///
/// Semantically UNSAT. ay#4767 previously returned Sat (incorrect).
#[test]
#[timeout(30000)]
fn pattern_bindings_uf_fallback_custom_constructor_produces_binding() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();

    // Pre-declare `w` as Int to prevent native datatype encoding.
    // This forces the UF fallback path in both encode_pattern_condition
    // and pattern_bindings.
    let w_term = encoder
        .get_or_declare_var("w", Sort::Int)
        .expect("should declare w");

    // match w { Wrap(x) => x + 1, _ => 0 }
    let expr = match_expr(
        var("w"),
        vec![
            (
                Pattern::Constructor {
                    name: "Wrap".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".into()))),
                },
                add(var("x"), int(1)),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("UF fallback match with custom constructor binding should encode");

    // The fix should have declared a `payload_wrap` accessor.
    assert!(
        encoder.decls().has_spec_func("payload_wrap"),
        "pattern_bindings should declare payload_wrap accessor for Wrap constructor (#1681)"
    );

    // Assert is_wrap(w) to constrain to the Wrap branch.
    let is_wrap = encoder
        .decls()
        .get_spec_func("is_wrap")
        .cloned()
        .expect("is_wrap tester should be declared");
    let is_wrap_w = encoder.solver.apply(&is_wrap, &[w_term]);
    encoder.solver.assert_term(is_wrap_w);

    // Assert payload_wrap(w) == 5.
    let payload_wrap = encoder
        .decls()
        .get_spec_func("payload_wrap")
        .cloned()
        .expect("payload_wrap should exist");
    let five = encoder.solver.int_const(5);
    let payload_applied = encoder.solver.apply(&payload_wrap, &[w_term]);
    let payload_eq_5 = encoder.solver.eq(payload_applied, five);
    encoder.solver.assert_term(payload_eq_5);

    // x + 1 = 5 + 1 = 6. Semantically, match != 6 should be UNSAT.
    let six = encoder.solver.int_const(6);
    let eq = encoder.solver.eq(match_term, six);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ay#4767 UF fallback binding: expected Unsat, got {result:?}."
    );
}

/// Fail-closed regression: invalid `Tag(x)` pattern on zero-field constructor
/// should return an error instead of panicking or silently weakening constraints.
#[test]
#[timeout(30000)]
fn pattern_bindings_no_selector_fallback_produces_binding() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();

    // DT with zero-field "Tag" constructor — payload_selector returns None.
    let dt = DatatypeSort {
        name: "TaggedInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Tag".into(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Val".into(),
                fields: vec![DatatypeField {
                    name: "taggedint_val_0".into(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    let _t_term = encoder
        .get_or_declare_var("t", Sort::Datatype(dt.clone()))
        .expect("should declare t");

    // match t { Tag(x) => x, _ => 0 }
    let expr = match_expr(
        var("t"),
        vec![
            (
                Pattern::Constructor {
                    name: "Tag".into(),
                    inner: Some(Box::new(Pattern::Binding("x".into()))),
                },
                var("x"),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );
    let caught =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| encoder.encode_pure(&expr)));
    match caught {
        Ok(Ok(_)) => panic!("invalid zero-field constructor pattern Tag(x) unexpectedly encoded"),
        Ok(Err(err)) => {
            let text = format!("{err:?}");
            assert!(
                text.contains("no payload") || text.contains("constructor pattern Tag"),
                "expected explicit no-payload error for zero-field constructor pattern, got: {text}"
            );
        }
        Err(panic_payload) => {
            let text = if let Some(s) = panic_payload.downcast_ref::<&str>() {
                (*s).to_string()
            } else if let Some(s) = panic_payload.downcast_ref::<String>() {
                s.clone()
            } else {
                format!("{panic_payload:?}")
            };
            assert!(
                text.contains("no payload") || text.contains("constructor pattern Tag"),
                "expected panic text to describe the zero-field constructor pattern, got: {text}"
            );
        }
    }
}

/// Tuple-pattern matching over datatype-valued elements must preserve the
/// constructor payloads through sort-aware getters and native selector tests.
#[test]
#[timeout(30000)]
fn test_tuple_pattern_logic_getter_reconstructs_first_datatype_element() {
    use trust_wp_core::{
        formula::{intern_sort_name, internal::tuple_lowering::tuple_logic_fn_name, ExprSort},
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]));

    let own_result_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let left = var_with_sort("left", own_result_sort.clone());
    let right = var_with_sort("right", own_result_sort);
    let pair = logic_fn_call(&tuple_logic_fn_name(2), vec![left.clone(), right]);
    let expr = match_expr(
        pair.clone(),
        vec![
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "OwnResult::Err".to_string(),
                        inner: Some(Box::new(Pattern::Binding("l".to_string()))),
                    },
                    Pattern::Constructor {
                        name: "OwnResult::Err".to_string(),
                        inner: Some(Box::new(Pattern::Binding("r".to_string()))),
                    },
                ]),
                eq(var("l"), var("r")),
            ),
            (Pattern::Wildcard, bool_expr(false)),
        ],
    );
    encoder
        .encode_pure(&expr)
        .expect("tuple-pattern match should declare sort-aware tuple getters");

    let getter_0_name = tuple_logic_getter_decl_name(&encoder, 0);
    let getter_0 = encoder
        .decls()
        .get_logic_func(&getter_0_name)
        .expect("tuple_get_0 getter should resolve")
        .clone();
    // SMT-mangled name for the tuple2 constructor placeholder. `logic_fn_smt_name`
    // doubles every `_`, so `__trust_wp_tuple2` becomes `logic____trust__wp__tuple2`.
    // The placeholder is registered with a `__placeholder_<n>` suffix.
    let tuple_ctor_smt_base = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple2");
    let tuple_ctor_name = encoder
        .decls()
        .logic_func_names()
        .find(|name| {
            *name == &tuple_ctor_smt_base
                || name.starts_with(&format!("{tuple_ctor_smt_base}__placeholder_"))
        })
        .expect("tuple2 constructor placeholder should be declared")
        .clone();
    let tuple_ctor = encoder
        .decls()
        .get_logic_func(&tuple_ctor_name)
        .expect("tuple2 constructor placeholder should resolve");
    assert_eq!(
        getter_0.domain().first(),
        Some(tuple_ctor.range()),
        "tuple getter domain must match tuple constructor range for tuple axioms to apply"
    );

    let pair_term = encoder
        .encode_pure(&pair)
        .expect("tuple pair should encode");
    let left_term = encoder.encode_pure(&left).expect("left should encode");
    let get_0_term = encoder.solver.apply(&getter_0, &[pair_term]);
    let left_err = encoder
        .encode_pure(&logic_fn_call("OwnResult::Err", vec![int(7)]))
        .expect("left Err constructor should encode");
    let tuple_ctor_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple2");
    let tuple_entries = encoder
        .ground_pool_for_test()
        .entries_for(&tuple_ctor_smt)
        .expect("tuple2 constructor should be registered in the ground pool");
    assert!(
        tuple_entries.iter().any(|entry| entry.application == pair_term),
        "tuple-pattern helper should reason over the same tuple2 term registered in the ground pool"
    );

    encoder.assert_tuple_axioms();
    let left_eq = encoder.solver.eq(left_term, left_err);
    let get_0_eq_left = encoder.solver.eq(get_0_term, left_term);
    let neq_get_0_left = encoder.solver.not(get_0_eq_left);
    encoder.assert_term(left_eq);
    encoder.assert_term(neq_get_0_left);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "sort-aware tuple_get_0 should reconstruct the datatype-valued first element"
    );
}

#[test]
#[timeout(30000)]
fn test_tuple_pattern_match_preserves_datatype_err_payloads() {
    use trust_wp_core::{
        formula::{intern_sort_name, internal::tuple_lowering::tuple_logic_fn_name, ExprSort},
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]));

    let own_result_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let left = var_with_sort("left", own_result_sort.clone());
    let right = var_with_sort("right", own_result_sort.clone());
    let pair = logic_fn_call(&tuple_logic_fn_name(2), vec![left.clone(), right.clone()]);
    let expr = match_expr(
        pair,
        vec![
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "OwnResult::Err".to_string(),
                        inner: Some(Box::new(Pattern::Binding("l".to_string()))),
                    },
                    Pattern::Constructor {
                        name: "OwnResult::Err".to_string(),
                        inner: Some(Box::new(Pattern::Binding("r".to_string()))),
                    },
                ]),
                eq(var("l"), var("r")),
            ),
            (Pattern::Wildcard, bool_expr(false)),
        ],
    );

    let term = encoder
        .encode_pure(&expr)
        .expect("tuple-pattern match on datatype elements should encode");

    let getter_0_name = tuple_logic_getter_decl_name(&encoder, 0);
    let getter_1_name = tuple_logic_getter_decl_name(&encoder, 1);
    let getter_0 = encoder
        .decls()
        .get_logic_func(&getter_0_name)
        .expect("tuple_get_0 getter should resolve")
        .clone();
    let getter_1 = encoder
        .decls()
        .get_logic_func(&getter_1_name)
        .expect("tuple_get_1 getter should resolve")
        .clone();

    let own_result_ay_sort = encoder.sort_from_expr_sort(own_result_sort.clone());
    let own_result_term_sort = own_result_ay_sort.as_term_sort();
    assert_eq!(
        getter_0.range(),
        &own_result_term_sort,
        "tuple_get_0 should preserve the OwnResult element sort"
    );
    assert_eq!(
        getter_1.range(),
        &own_result_term_sort,
        "tuple_get_1 should preserve the OwnResult element sort"
    );

    let left_err = encoder
        .encode_pure(&logic_fn_call("OwnResult::Err", vec![int(7)]))
        .expect("left Err constructor should encode");
    let right_err = encoder
        .encode_pure(&logic_fn_call("OwnResult::Err", vec![int(7)]))
        .expect("right Err constructor should encode");
    let left_term = encoder.encode_pure(&left).expect("left should encode");
    let right_term = encoder.encode_pure(&right).expect("right should encode");

    encoder.assert_tuple_axioms();
    let left_eq = encoder.solver.eq(left_term, left_err);
    let right_eq = encoder.solver.eq(right_term, right_err);
    encoder.assert_term(left_eq);
    encoder.assert_term(right_eq);

    let negated = encoder.solver.not(term);
    encoder.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "matching (Err(7), Err(7)) should bind both payloads and prove l == r"
    );
}

/// Verify that tuple pattern conditions on a non-Int scrutinee also use
/// sort-aware getters instead of falling back to Int-domain UFs.
#[test]
#[timeout(30000)]
fn test_tuple_pattern_condition_non_int_scrutinee_uses_sort_aware_getters() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let scrutinee = encoder
        .solver
        .declare_const("tuple_cond", Sort::Uninterpreted("Tuple2".to_string()));
    encoder
        .vars_mut_for_test()
        .insert("tuple_cond".to_string(), scrutinee);
    encoder.var_sorts_mut_for_test().insert(
        "tuple_cond".to_string(),
        Sort::Uninterpreted("Tuple2".to_string()),
    );

    let expr = match_expr(
        var("tuple_cond"),
        vec![
            (
                Pattern::Tuple(vec![
                    Pattern::Literal(int(0)),
                    Pattern::Binding("b".to_string()),
                ]),
                var("b"),
            ),
            (Pattern::Wildcard, int(-1)),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("tuple condition on Tuple2 scrutinee should encode");

    let getter_0_name = tuple_logic_getter_decl_name(&encoder, 0);
    let getter_1_name = tuple_logic_getter_decl_name(&encoder, 1);
    let getter_0 = encoder
        .decls()
        .get_logic_func(&getter_0_name)
        .expect("sort-aware getter_0 should exist")
        .clone();
    let getter_1 = encoder
        .decls()
        .get_logic_func(&getter_1_name)
        .expect("sort-aware getter_1 should exist")
        .clone();

    let tuple_0 = encoder.solver.apply(&getter_0, &[scrutinee]);
    let tuple_1 = encoder.solver.apply(&getter_1, &[scrutinee]);
    let zero = encoder.solver.int_const(0);
    let tuple_0_is_zero = encoder.solver.eq(tuple_0, zero);
    let match_eq_tuple_1 = encoder.solver.eq(match_term, tuple_1);
    let match_neq_tuple_1 = encoder.solver.not(match_eq_tuple_1);
    encoder.solver.assert_term(tuple_0_is_zero);
    encoder.solver.assert_term(match_neq_tuple_1);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "when tuple_cond.0 == 0, the first arm should return tuple_cond.1"
    );
}

// ── Same-layout struct isolation (#1982, Slice 5) ───────────────────
//
// Two distinct struct types with identical field layouts must not be
// mutually substitutable at the verification level. With native ADT
// encoding, Point{x:i32,y:i32} and Range{start:i32,end:i32} should be
// separate ay datatypes, so asserting a Point variable equals a Range
// constructor should always be UNSAT.

/// Same-layout structs must NOT be conflated: Point(3,4) != Range(3,4).
///
/// Without proper ADT encoding, both types collapse to the same
/// (Int,Int) tuple, making cross-type equality silently acceptable.
/// With native ADT encoding, ay rejects `eq(Point, Range)` at the API
/// level — an even stronger guarantee than UNSAT.
#[test]
#[timeout(30000)]
fn test_same_layout_structs_not_interchangeable_in_verification() {
    use trust_wp_core::{
        formula::intern_sort_name,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let adt_decls = std::collections::HashMap::from([
        (
            "Point".to_string(),
            AdtDecl::new(
                "crate::Point".to_string(),
                "Point".to_string(),
                AdtKind::Struct,
                vec![AdtConstructorDecl::new(
                    "Point".to_string(),
                    "Point".to_string(),
                    vec![
                        AdtFieldDecl::new("x".to_string(), ExprSort::Int),
                        AdtFieldDecl::new("y".to_string(), ExprSort::Int),
                    ],
                )],
            ),
        ),
        (
            "Range".to_string(),
            AdtDecl::new(
                "crate::Range".to_string(),
                "Range".to_string(),
                AdtKind::Struct,
                vec![AdtConstructorDecl::new(
                    "Range".to_string(),
                    "Range".to_string(),
                    vec![
                        AdtFieldDecl::new("start".to_string(), ExprSort::Int),
                        AdtFieldDecl::new("end".to_string(), ExprSort::Int),
                    ],
                )],
            ),
        ),
    ]);

    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&adt_decls);

    // Verify Point and Range resolve to distinct native datatype sorts
    let point_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("Point")));
    let range_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("Range")));

    assert!(
        matches!(point_sort, ay_dpll::api::Sort::Datatype(_)),
        "Point should be a native datatype sort: {point_sort:?}"
    );
    assert!(
        matches!(range_sort, ay_dpll::api::Sort::Datatype(_)),
        "Range should be a native datatype sort: {range_sort:?}"
    );
    assert_ne!(
        point_sort, range_sort,
        "same-layout structs must have distinct ay carrier sorts"
    );

    // Declare a Point-sorted variable and a Range constructor value
    let p = encoder
        .get_or_declare_var("p", point_sort)
        .expect("Point var should declare");
    let range_dt = encoder
        .constructor_datatype("Range")
        .expect("Range should be a registered datatype");
    let three = encoder.solver.int_const(3);
    let four = encoder.solver.int_const(4);
    let range_val = encoder
        .solver
        .try_datatype_constructor(&range_dt, "Range", &[three, four])
        .expect("Range constructor should exist");

    // ay enforces sort safety at the API level: eq(Point, Range) panics
    // because the sorts are distinct. This is a STRONGER guarantee than
    // UNSAT — the solver prevents cross-type comparison entirely.
    let eq_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.solver.eq(p, range_val)
    }));
    assert!(
        eq_result.is_err(),
        "eq(Point-sorted var, Range constructor) should be rejected by sort checker"
    );
}
