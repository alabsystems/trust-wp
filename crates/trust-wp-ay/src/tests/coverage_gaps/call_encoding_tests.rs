// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for logic function call-site encoding (`call_encoding.rs`).
//!
//! Covers: `encode_logic_fn_call_impl` builtin dispatch, `apply_logic_fn`
//! placeholder creation and sort coercion, `infer_expr_sort_with_context`.
//!
//! Part of #2514 (Tier 2 coverage gap: call_encoding.rs, 606 LOC, zero tests).

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use super::super::{super::*, helpers::*};

// ── encode_logic_fn_call_impl: builtin dispatch ─────────────────────

/// `seq![v]` single-element dispatches to seq_singleton.
#[test]
#[timeout(30000)]
fn builtin_seq_singleton() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("seq", vec![int(42)]);
    let term = encoder.encode_pure(&expr).expect("seq singleton encoding");
    let sort = encoder.solver.get_sort(term);
    assert!(
        sort.is_seq(),
        "seq![42] should produce a Seq-sorted term, got {sort:?}"
    );
}

/// `seq![v1, v2, v3]` multi-element dispatches to fresh constant with Array backing.
#[test]
#[timeout(30000)]
fn builtin_seq_multi_element() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("seq", vec![int(1), int(2), int(3)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("seq multi-element encoding");
    let sort = encoder.solver.get_sort(term);
    assert!(
        sort.is_seq(),
        "seq![1, 2, 3] should produce a Seq-sorted term, got {sort:?}"
    );
}

/// `seq_empty` dispatches to the axiom-backed empty sequence.
#[test]
#[timeout(30000)]
fn builtin_seq_empty() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("seq_empty", vec![]);
    let term = encoder.encode_pure(&expr).expect("seq_empty encoding");
    let sort = encoder.solver.get_sort(term);
    assert!(
        sort.is_seq(),
        "seq_empty should produce a Seq-sorted term, got {sort:?}"
    );
}

/// `Seq::empty()` is an alias for `seq_empty`.
#[test]
#[timeout(30000)]
fn builtin_seq_empty_method_syntax() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("Seq::empty", vec![]);
    let term = encoder.encode_pure(&expr).expect("Seq::empty encoding");
    let sort = encoder.solver.get_sort(term);
    assert!(
        sort.is_seq(),
        "Seq::empty() should produce a Seq-sorted term, got {sort:?}"
    );
}

/// `__trust_wp_tuple0()` (unit value) produces a Unit-sorted constant.
#[test]
#[timeout(30000)]
fn builtin_tuple0_unit() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("__trust_wp_tuple0", vec![]);
    let term = encoder.encode_pure(&expr).expect("tuple0 encoding");
    let sort = encoder.solver.get_sort(term);
    assert!(
        matches!(&sort, Sort::Uninterpreted(s) if s == "Unit"),
        "__trust_wp_tuple0() should produce a Unit-sorted term, got {sort:?}"
    );
}

/// `__trust_wp_concrete_float_*` returns an unsupported error.
#[test]
#[timeout(30000)]
fn builtin_concrete_float_rejected() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("__trust_wp_concrete_float_1_5", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "concrete float literals should be rejected with unsupported error"
    );
}

// ── apply_logic_fn: placeholder creation ────────────────────────────

/// Calling an undeclared logic function creates a placeholder UF declaration.
#[test]
#[timeout(30000)]
fn placeholder_created_for_unknown_fn() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("unknown_fn", vec![int(1)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("placeholder should be created");
    let _ = encoder.solver.get_sort(term);
}

/// Two calls with the same name but different argument sorts get
/// distinct placeholder declarations (sort-keyed naming).
#[test]
#[timeout(30000)]
fn placeholder_distinct_for_different_sorts() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // First call with Int argument
    let int_call = logic_fn_call("poly_fn", vec![int(1)]);
    let int_term = encoder
        .encode_pure(&int_call)
        .expect("int-param placeholder");

    // Second call with Bool argument
    let bool_call = logic_fn_call("poly_fn", vec![bool_expr(true)]);
    let bool_term = encoder
        .encode_pure(&bool_call)
        .expect("bool-param placeholder");

    // Both should produce valid terms — the placeholder system handles
    // mixed sorts without crashing
    let _ = encoder.solver.get_sort(int_term);
    let _ = encoder.solver.get_sort(bool_term);
}

/// `apply_logic_fn` without `arg_exprs` rejects non-constructor functions.
#[test]
#[timeout(30000)]
fn apply_logic_fn_rejects_non_constructor_without_exprs() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dummy = encoder.solver.int_const(1);
    let result = encoder.apply_logic_fn("custom_fn", &[dummy], None, None);
    assert!(
        result.is_err(),
        "non-constructor function without arg_exprs should fail"
    );
}

/// `apply_logic_fn` without `arg_exprs` allows Some/Ok/Err (constructor fallback).
#[test]
#[timeout(30000)]
fn apply_logic_fn_allows_constructors_without_exprs() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dummy = encoder.solver.int_const(42);

    for ctor in &[
        "Some",
        "Ok",
        "Err",
        "Option::Some",
        "Result::Ok",
        "Result::Err",
    ] {
        let result = encoder.apply_logic_fn(ctor, &[dummy], None, None);
        assert!(
            result.is_ok(),
            "constructor {ctor} should succeed without arg_exprs"
        );
    }
}

// ── apply_logic_fn: sort coercion on declared functions ─────────────

/// When a declared function has domain sort X but the argument has sort Y,
/// `apply_logic_fn` coerces by replacing with a fresh constant.
#[test]
#[timeout(30000)]
fn apply_logic_fn_coerces_mismatched_arg_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare a function with the SMT name that apply_logic_fn will look up.
    // logic_fn_smt_name("boolfn") = "logic_boolfn"
    let _fd = encoder.get_or_declare_logic_func("logic_boolfn", &[Sort::Bool], Sort::Bool);

    // Apply with an Int argument — should coerce (fresh Bool constant)
    let int_arg = encoder.solver.int_const(42);
    let result = encoder.apply_logic_fn("boolfn", &[int_arg], None, None);
    assert!(
        result.is_ok(),
        "sort coercion should produce a valid term instead of crashing"
    );
    let term = result.unwrap();
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Bool,
        "result should have the declared return sort Bool"
    );
}

// ── infer_expr_sort_with_context ────────────────────────────────────

/// Known logic function returns the declared range sort.
#[test]
#[timeout(30000)]
fn infer_sort_from_declared_logic_fn() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    // logic_fn_smt_name("isvalid") = "logic_isvalid" (no underscores to double)
    let _fd = encoder.get_or_declare_logic_func("logic_isvalid", &[Sort::Int], Sort::Bool);

    let expr = logic_fn_call("isvalid", vec![int(0)]);
    let sort = encoder.infer_expr_sort_with_context(&expr, None);
    assert_eq!(
        sort,
        Sort::Bool,
        "declared logic function should return its declared range sort"
    );
}

/// Unknown logic function with sort hint returns the hinted sort.
#[test]
#[timeout(30000)]
fn infer_sort_from_sort_hint() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    // logic_fn_smt_name("hintedfn") = "logic_hintedfn"
    encoder.record_sort_hint("logic_hintedfn".to_string(), ExprSort::Bool);

    let expr = logic_fn_call("hintedfn", vec![int(0)]);
    let sort = encoder.infer_expr_sort_with_context(&expr, None);
    assert_eq!(
        sort,
        Sort::Bool,
        "undeclared function with Bool hint should infer Bool"
    );
}

/// Declared native constructors must infer their datatype sort without
/// falling through to the generic LogicFn Int fallback.
#[test]
#[timeout(30000)]
fn infer_sort_from_declared_native_constructor() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new_with_quantifiers();
    let own_result = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_err_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&own_result);

    let expr = logic_fn_call("OwnResult::Ok", vec![int(0)]);
    let sort = encoder.infer_expr_sort_with_context(&expr, None);
    assert_eq!(
        sort,
        Sort::Datatype(own_result),
        "declared native constructor should infer its datatype sort"
    );
}

/// Unknown logic function without hints falls back to Int.
#[test]
#[timeout(30000)]
fn infer_sort_fallback_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("totally_unknown", vec![int(0)]);
    let sort = encoder.infer_expr_sort_with_context(&expr, None);
    assert_eq!(
        sort,
        Sort::Int,
        "undeclared function without hints should default to Int"
    );
}

/// Non-LogicFnCall expressions delegate to infer_encoded_sort.
#[test]
#[timeout(30000)]
fn infer_sort_non_logic_fn_delegates() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let int_expr = int(42);
    assert_eq!(
        encoder.infer_expr_sort_with_context(&int_expr, None),
        Sort::Int
    );

    let bool_expr_val = bool_expr(true);
    assert_eq!(
        encoder.infer_expr_sort_with_context(&bool_expr_val, None),
        Sort::Bool
    );
}

// ── resolve builtin ─────────────────────────────────────────────────

/// `resolve(x)` on a mutable reference encodes as `x_current == x_final`.
#[test]
#[timeout(30000)]
fn builtin_resolve_encodes_current_eq_final() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare both current and final versions of x
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("x current");
    encoder
        .get_or_declare_var("x_final", Sort::Int)
        .expect("x final");

    let expr = logic_fn_call("resolve", vec![var("x")]);
    let term = encoder.encode_pure(&expr).expect("resolve encoding");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Bool,
        "resolve(x) should produce a Bool-sorted equality term"
    );
}

// ── Ground pool registration ────────────────────────────────────────

/// Logic function calls outside quantifiers register in the ground pool.
#[test]
#[timeout(30000)]
fn ground_pool_registration_at_depth_zero() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare a function so ground pool can register it
    let _fd = encoder.get_or_declare_logic_func("logic_gp_fn", &[Sort::Int], Sort::Int);

    let expr = logic_fn_call("gp_fn", vec![int(1)]);
    let _term = encoder.encode_pure(&expr).expect("encode for ground pool");

    // The ground pool should now have at least one entry
    // (We can't inspect the pool directly, but the encoding should not fail)
}

// ── Bool→Int coercion for Option/Result constructors ────────────────

/// `Some(true)` coerces Bool to Int (ite true 1 0) for the UF fallback path.
#[test]
#[timeout(30000)]
fn constructor_bool_to_int_coercion() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Without datatype declarations, Some goes through the UF fallback path
    let expr = logic_fn_call("Some", vec![bool_expr(true)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Some(true) should encode via Bool→Int coercion");
    let _ = encoder.solver.get_sort(term);
}

/// `Err(false)` also coerces via the same path.
#[test]
#[timeout(30000)]
fn constructor_err_bool_coercion() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let expr = logic_fn_call("Err", vec![bool_expr(false)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Err(false) should encode via Bool→Int coercion");
    let _ = encoder.solver.get_sort(term);
}

/// Qualified stdlib `Option::Some` must preserve the Option carrier sort even
/// when its payload forces a fallback away from the native constructor path.
#[test]
#[timeout(30000)]
fn qualified_option_some_fallback_preserves_option_sort_for_custom_payload() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    use crate::encoder::match_enc::SwitchTarget;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let own_result = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_err_error".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&own_result);

    let expr = logic_fn_call(
        "Option::Some",
        vec![logic_fn_call("OwnResult::Err", vec![int(7)])],
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("Option::Some(OwnResult::Err(7)) should encode on the placeholder path");
    let sort = encoder.solver.get_sort(term);
    assert!(
        sort == Sort::Datatype(SwitchTarget::OptionInt.datatype())
            || sort == Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name),
        "qualified stdlib Some fallback should keep the OptionInt carrier sort family, got {sort:?}"
    );
}

// ── #1552: ResultIntInt placeholder sort inference ───────────────────

/// `Result::Ok(x)` on the placeholder path must produce a ResultIntInt-sorted
/// term, not Int. Before #1552, `placeholder_return_sort` only handled
/// OptionInt, so Ok/Err fell through to Sort::Int.
#[test]
#[timeout(30000)]
fn result_ok_placeholder_gets_result_datatype_sort() {
    use crate::encoder::match_enc::SwitchTarget;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("Result::Ok", vec![int(42)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Result::Ok(42) should encode without sort mismatch");
    let sort = encoder.solver.get_sort(term);
    let result_dt = SwitchTarget::ResultIntInt.datatype();
    assert!(
        sort == Sort::Datatype(result_dt.clone())
            || sort == Sort::Uninterpreted(result_dt.name.clone()),
        "Result::Ok placeholder should have ResultIntInt sort, got {sort:?}"
    );
}

/// `Result::Err(x)` on the placeholder path must also produce ResultIntInt.
#[test]
#[timeout(30000)]
fn result_err_placeholder_gets_result_datatype_sort() {
    use crate::encoder::match_enc::SwitchTarget;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("Result::Err", vec![int(99)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Result::Err(99) should encode without sort mismatch");
    let sort = encoder.solver.get_sort(term);
    let result_dt = SwitchTarget::ResultIntInt.datatype();
    assert!(
        sort == Sort::Datatype(result_dt.clone())
            || sort == Sort::Uninterpreted(result_dt.name.clone()),
        "Result::Err placeholder should have ResultIntInt sort, got {sort:?}"
    );
}

// ── #1552: FMap-returning function placeholder sort inference ────────

/// `fmap_insert(m, k, v)` on the placeholder path must return FMap sort.
#[test]
#[timeout(30000)]
fn fmap_insert_placeholder_gets_fmap_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("fmap_insert", vec![int(0), int(1), int(2)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("fmap_insert should encode with FMap sort");
    let sort = encoder.solver.get_sort(term);
    assert!(
        matches!(&sort, Sort::Uninterpreted(s) if s == "FMap"),
        "fmap_insert placeholder should have FMap sort, got {sort:?}"
    );
}

/// `fmap_merge(a, b)` on the placeholder path must return FMap sort.
#[test]
#[timeout(30000)]
fn fmap_merge_placeholder_gets_fmap_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = logic_fn_call("fmap_merge", vec![int(0), int(1)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("fmap_merge should encode with FMap sort");
    let sort = encoder.solver.get_sort(term);
    assert!(
        matches!(&sort, Sort::Uninterpreted(s) if s == "FMap"),
        "fmap_merge placeholder should have FMap sort, got {sort:?}"
    );
}

// ── Result constructor auto-registration (#2207) ────────────────────

/// `Ok(1)` should auto-register ResultIntInt and produce Datatype-sorted term.
///
/// Before #2207 fix, `try_auto_register_stdlib_constructor` only handled
/// OptionInt, so Ok/Err fell through to the UF placeholder path with
/// `Int → Datatype(ResultIntInt)` return sort. This created a disconnect
/// between the UF-based encoding and the Int-based axiom system in
/// `assert_option_result_axioms`, which expects `Int → Int` constructors.
/// The fix extends auto-registration to ResultIntInt so Ok/Err use native
/// datatype constructors directly. (#2207)
#[test]
#[timeout(30000)]
fn result_ok_auto_registers_native_datatype() {
    let mut encoder = AYEncoder::new();
    let expr = logic_fn_call("Ok", vec![int(42)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Ok(42) should encode via native constructor");
    let sort = encoder.solver.get_sort(term);
    let is_result = matches!(&sort, Sort::Datatype(dt) if dt.name == "ResultIntInt")
        || matches!(&sort, Sort::Uninterpreted(name) if name == "ResultIntInt");
    assert!(
        is_result,
        "Ok(42) should produce ResultIntInt sort, got {sort:?}"
    );
}

/// `Err(99)` should auto-register ResultIntInt and produce Datatype-sorted term.
#[test]
#[timeout(30000)]
fn result_err_auto_registers_native_datatype() {
    let mut encoder = AYEncoder::new();
    let expr = logic_fn_call("Err", vec![int(99)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Err(99) should encode via native constructor");
    let sort = encoder.solver.get_sort(term);
    let is_result = matches!(&sort, Sort::Datatype(dt) if dt.name == "ResultIntInt")
        || matches!(&sort, Sort::Uninterpreted(name) if name == "ResultIntInt");
    assert!(
        is_result,
        "Err(99) should produce ResultIntInt sort, got {sort:?}"
    );
}

/// `Err(x).is_ok()` should be provably false via native datatype tester.
///
/// Verifies the end-to-end path: auto-registration produces a native
/// Datatype(ResultIntInt) term, is_ok uses the native tester, and ay's
/// datatype theory proves is-Ok(Err(x)) = false without needing the
/// legacy UF axiom system. (#2207)
#[test]
#[timeout(30000)]
fn result_err_is_ok_false_via_native_tester() {
    use ay_dpll::api::SolveResult;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let is_ok_err = method_call(logic_fn_call("Err", vec![int(1)]), "is_ok", vec![]);
    let is_ok_term = encoder
        .encode_pure(&is_ok_err)
        .expect("Err(1).is_ok() should encode");
    // is_ok(Err(1)) should be provably false — assert it and expect UNSAT
    encoder.assert_term(is_ok_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Err(1).is_ok() should be UNSAT via native datatype discrimination (#2207)"
    );
}

/// `Ok(42).unwrap()` should extract payload via native datatype selector.
#[test]
#[timeout(30000)]
fn result_ok_unwrap_via_native_selector() {
    use ay_dpll::api::SolveResult;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let unwrap_ok = method_call(logic_fn_call("Ok", vec![int(42)]), "unwrap", vec![]);
    let unwrap_term = encoder
        .encode_pure(&unwrap_ok)
        .expect("Ok(42).unwrap() should encode");
    let forty_two = encoder.encode_pure(&int(42)).unwrap();
    // unwrap(Ok(42)) should equal 42
    let neq = {
        let eq = encoder.solver.eq(unwrap_term, forty_two);
        encoder.solver.not(eq)
    };
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Ok(42).unwrap() != 42 should be UNSAT via native selector (#2207)"
    );
}
