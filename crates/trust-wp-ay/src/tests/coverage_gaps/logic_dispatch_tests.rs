// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `encoder/method_call/logic_dispatch.rs`.
//!
//! Tests `try_logic_fn_dispatch` and `encode_structural_receiver_with_expected_sort`
//! through the public `encode_pure` API by registering logic functions and encoding
//! `MethodCall` expressions that trigger the dispatch path.
//!
//! Coverage targets:
//! - `try_logic_fn_dispatch`: registered logic fn takes precedence in method dispatch
//! - structural field receiver hint path (non-Int receiver sort triggers placeholder)
//! - `encode_structural_receiver_with_expected_sort`: creates placeholder declarations
//! - ground pool registration at quantifier_depth == 0 in hint path
//! - semantic correctness of dispatched terms (SAT/UNSAT)

use ay_dpll::api::Sort;
use ntest::timeout;

use super::*;

fn encode_placeholder_tag(raw: &str) -> String {
    let mut encoded = String::new();
    for byte in raw.as_bytes() {
        let _ = std::fmt::Write::write_fmt(&mut encoded, format_args!("{byte:02x}"));
    }
    encoded
}

fn canonical_placeholder_sort_tag(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "b".to_string(),
        Sort::Int => "i".to_string(),
        Sort::Uninterpreted(name) => format!("u{}", encode_placeholder_tag(name)),
        Sort::Datatype(dt) => format!("d{}", encode_placeholder_tag(&dt.name)),
        other => format!("x{}", encode_placeholder_tag(&format!("{other:?}"))),
    }
}

// ── Registered logic function dispatches via method call ─────────────

/// A registered logic function should be found by method dispatch.
/// Register `logic_my_spec : Int -> Int`, then encode `x.my_spec()`.
/// The dispatch path in `method_call/mod.rs` calls `try_logic_fn_dispatch`
/// for unrecognized methods, which should find the registered function.
#[test]
#[timeout(30000)]
fn test_registered_logic_fn_dispatches_via_method_call() {
    let mut encoder = AYEncoder::new();

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("my_spec");
    let decl = encoder
        .solver_mut()
        .declare_fun(&smt_name, &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, decl);

    let expr = method_call(var("x"), "my_spec", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "registered logic function should encode via method call: {result:?}"
    );
}

/// Multi-arg dispatch: register `logic_combine : (Int, Int, Int) -> Int`,
/// then encode `self.combine(a, b)`. The receiver becomes the first arg.
#[test]
#[timeout(30000)]
fn test_registered_logic_fn_multi_arg_dispatch() {
    let mut encoder = AYEncoder::new();

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("combine");
    let decl =
        encoder
            .solver_mut()
            .declare_fun(&smt_name, &[Sort::Int, Sort::Int, Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, decl);

    let expr = method_call(var("self"), "combine", vec![var("a"), var("b")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "multi-arg logic function should encode: {result:?}"
    );
}

// ── Structural field receiver hint path ─────────────────────────────

/// When the receiver is a tuple-field access `__trust_wp_tuple_get_0(x)` and
/// the registered logic function expects a non-Int receiver sort, the hint
/// path in `try_logic_fn_dispatch` creates a placeholder declaration to
/// bridge the sort gap. Test via encode_pure on the full expression.
#[test]
#[timeout(30000)]
fn test_tuple_field_receiver_with_non_int_sort_hint() {
    let mut encoder = AYEncoder::new();

    // Register a logic function that expects a non-Int sort
    let custom_sort = Sort::Uninterpreted("Seq_Int".to_string());
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("my_len");
    let decl = encoder
        .solver_mut()
        .declare_fun(&smt_name, &[custom_sort.clone()], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name.clone(), decl);

    // Encode: __trust_wp_tuple_get_0(result).my_len()
    // The receiver is a structural field (tuple prefix), and the expected
    // sort is non-Int, so the hint path should fire.
    let receiver = get_field(0, var("result"));
    let expr = method_call(receiver.clone(), "my_len", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "tuple-field receiver with non-Int hint should encode: {result:?}"
    );
    let entries = encoder
        .ground_pool_for_test()
        .entries_for(&smt_name)
        .expect("hint-path dispatch should register a ground application");
    assert_eq!(
        entries.len(),
        1,
        "hint-path dispatch should register exactly one ground application: {entries:?}"
    );
    assert_eq!(
        entries[0].arg_exprs,
        vec![receiver],
        "ground-pool entry should preserve the structural receiver expression"
    );
    assert!(
        entries[0].path_conditions.is_empty(),
        "top-level hint-path dispatch should not register path conditions"
    );
}

/// Named-field receivers (`__trust_wp_field_value(x)`) should also trigger
/// the structural field hint path.
#[test]
#[timeout(30000)]
fn test_named_field_receiver_with_non_int_sort_hint() {
    let mut encoder = AYEncoder::new();

    let dt_sort = Sort::Uninterpreted("MyStruct".to_string());
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("process");
    let decl = encoder
        .solver_mut()
        .declare_fun(&smt_name, &[dt_sort.clone()], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, decl);

    // Named-field receiver: __trust_wp_field_value(self).process()
    let receiver = named_field("value", var("self"));
    let expr = method_call(receiver, "process", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "named-field receiver with non-Int hint should encode: {result:?}"
    );
}

/// When the registered logic function expects Int for the first parameter,
/// the hint path should NOT fire (guard: `*sort != Sort::Int`). Normal
/// dispatch should still succeed.
#[test]
#[timeout(30000)]
fn test_tuple_field_receiver_with_int_sort_skips_hint() {
    let mut encoder = AYEncoder::new();

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("my_int_fn");
    let decl = encoder
        .solver_mut()
        .declare_fun(&smt_name, &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, decl);

    // Tuple-field receiver: __trust_wp_tuple_get_0(result).my_int_fn()
    let receiver = get_field(0, var("result"));
    let expr = method_call(receiver, "my_int_fn", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "tuple-field receiver with Int sort should still encode: {result:?}"
    );
}

// ── Placeholder reuse: same signature shares declaration ────────────

/// Two method calls with the same tuple-field receiver structure and same
/// target sort should reuse the same placeholder declaration (the decl_key
/// is deterministic from sort tags). Verify that both encode successfully.
#[test]
#[timeout(30000)]
fn test_placeholder_reused_across_calls() {
    let mut encoder = AYEncoder::new();

    let custom_sort = Sort::Uninterpreted("FMap_Int".to_string());
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("my_size");
    let decl = encoder
        .solver_mut()
        .declare_fun(&smt_name, &[custom_sort.clone()], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, decl);
    let getter_name =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let getter_smt_name = trust_wp_core::logic::logic_fn_smt_name(&getter_name);
    let placeholder_prefix = format!("{getter_smt_name}__placeholder_");

    // First call with receiver __trust_wp_tuple_get_0(x)
    let expr1 = method_call(get_field(0, var("x")), "my_size", vec![]);
    let r1 = encoder.encode_pure(&expr1);
    assert!(r1.is_ok(), "first placeholder call should succeed: {r1:?}");
    let placeholder_names_after_first = encoder
        .decls()
        .logic_func_names()
        .filter(|name| name.starts_with(&placeholder_prefix))
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(
        placeholder_names_after_first.len(),
        1,
        "first placeholder call should create exactly one placeholder decl: \
         {placeholder_names_after_first:?}"
    );

    // Second call with receiver __trust_wp_tuple_get_0(y) — same field index,
    // same expected sort → should reuse the placeholder declaration.
    let expr2 = method_call(get_field(0, var("y")), "my_size", vec![]);
    let r2 = encoder.encode_pure(&expr2);
    assert!(
        r2.is_ok(),
        "second placeholder call should reuse declaration: {r2:?}"
    );
    let placeholder_names_after_second = encoder
        .decls()
        .logic_func_names()
        .filter(|name| name.starts_with(&placeholder_prefix))
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(
        placeholder_names_after_second.len(),
        1,
        "reused placeholder path should not declare a second placeholder: \
         {placeholder_names_after_second:?}"
    );
    assert_eq!(
        placeholder_names_after_second, placeholder_names_after_first,
        "same receiver shape and expected sort should reuse the original placeholder decl"
    );
}

/// Structural receiver hinting must reuse the canonical placeholder family
/// created by the general logic-fn placeholder path, even when the hinted
/// receiver sort is Seq. Seq-specific `method_sort_tag` aliases (`ret_s`) are
/// not valid placeholder keys here because the rest of the placeholder system
/// still keys Seq returns by the canonical debug-sort hex tag. (#1988 audit)
#[test]
#[timeout(30000)]
fn test_structural_seq_hint_reuses_canonical_placeholder_family() {
    let mut encoder = AYEncoder::new();

    let getter_name =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let getter_smt_name = trust_wp_core::logic::logic_fn_smt_name(&getter_name);
    let seq_sort = Sort::seq(Sort::Int);
    let canonical_placeholder_name = format!(
        "{getter_smt_name}__placeholder_i__ret_{}",
        canonical_placeholder_sort_tag(&seq_sort)
    );
    let canonical_decl = encoder.solver_mut().declare_fun(
        &canonical_placeholder_name,
        &[Sort::Int],
        seq_sort.clone(),
    );
    encoder
        .decls_for_test_mut()
        .insert_logic_func(canonical_placeholder_name.clone(), canonical_decl);

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("my_len");
    let decl =
        encoder
            .solver_mut()
            .declare_fun(&smt_name, std::slice::from_ref(&seq_sort), Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, decl);

    let result = encoder.encode_pure(&method_call(get_field(0, var("x")), "my_len", vec![]));
    assert!(
        result.is_ok(),
        "Seq-typed structural receiver should reuse the canonical placeholder family: {result:?}"
    );

    let placeholder_prefix = format!("{getter_smt_name}__placeholder_");
    let mut placeholder_names = encoder
        .decls()
        .logic_func_names()
        .filter(|name| name.starts_with(&placeholder_prefix))
        .cloned()
        .collect::<Vec<_>>();
    placeholder_names.sort();
    assert_eq!(
        placeholder_names,
        vec![canonical_placeholder_name],
        "Seq structural receiver hint should not create a second placeholder family"
    );
}

// ── Semantic correctness: SAT/UNSAT with dispatched terms ───────────

/// Register a logic function `double(x)`, encode `x.double()`, assert
/// an axiom `double(5) == 10`, then check that `x=5 ∧ x.double()==10`
/// is SAT.
#[test]
#[timeout(30000)]
fn test_logic_dispatch_semantic_sat() {
    let mut encoder = AYEncoder::new();

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("double");
    let decl = encoder
        .solver_mut()
        .declare_fun(&smt_name, &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name.clone(), decl.clone());

    // Axiom: double(5) == 10
    let five_term = encoder.encode_pure(&int(5)).unwrap();
    let fn_app = encoder.solver_mut().apply(&decl, &[five_term]);
    let ten_term = encoder.encode_pure(&int(10)).unwrap();
    let axiom = encoder.solver_mut().eq(fn_app, ten_term);
    encoder.assert_term(axiom);

    // Encode x.double() via method dispatch (triggers try_logic_fn_dispatch)
    let x_eq_5 = eq(var("x"), int(5));
    let x_eq_5_term = encoder.encode_pure(&x_eq_5).unwrap();
    encoder.assert_term(x_eq_5_term);

    let call_expr = method_call(var("x"), "double", vec![]);
    let call_term = encoder.encode_pure(&call_expr).unwrap();
    let result_eq_10 = encoder.solver_mut().eq(call_term, ten_term);
    encoder.assert_term(result_eq_10);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "x=5 ∧ double(5)=10 ∧ x.double()==10 should be SAT"
    );
}

/// Semantic UNSAT: register `triple(x)`, axiom `triple(3)==9`, then assert
/// `x=3 ∧ x.triple() != 9` — should be UNSAT.
#[test]
#[timeout(30000)]
fn test_logic_dispatch_semantic_unsat() {
    let mut encoder = AYEncoder::new();

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("triple");
    let decl = encoder
        .solver_mut()
        .declare_fun(&smt_name, &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name.clone(), decl.clone());

    // Axiom: triple(3) == 9
    let three_term = encoder.encode_pure(&int(3)).unwrap();
    let fn_app = encoder.solver_mut().apply(&decl, &[three_term]);
    let nine_term = encoder.encode_pure(&int(9)).unwrap();
    let axiom = encoder.solver_mut().eq(fn_app, nine_term);
    encoder.assert_term(axiom);

    // x = 3
    let x_eq_3 = eq(var("x"), int(3));
    let x_eq_3_term = encoder.encode_pure(&x_eq_3).unwrap();
    encoder.assert_term(x_eq_3_term);

    // x.triple() != 9 (contradicts axiom)
    let call_expr = method_call(var("x"), "triple", vec![]);
    let call_term = encoder.encode_pure(&call_expr).unwrap();
    let result_eq_9 = encoder.solver_mut().eq(call_term, nine_term);
    let neg = encoder.solver_mut().not(result_eq_9);
    encoder.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=3 ∧ triple(3)==9 ∧ x.triple()!=9 should be UNSAT"
    );
}

// ── Non-structural receiver: plain var goes through normal dispatch ──

/// A plain variable receiver with a registered logic function should still
/// dispatch successfully (no hint path needed — only structural field
/// receivers trigger the hint path).
#[test]
#[timeout(30000)]
fn test_plain_var_receiver_dispatches_normally() {
    let mut encoder = AYEncoder::new();

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("norm");
    let decl = encoder
        .solver_mut()
        .declare_fun(&smt_name, &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, decl);

    let expr = method_call(var("x"), "norm", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "plain var receiver with registered logic fn should encode: {result:?}"
    );
}

// ── Hint path with extra args ───────────────────────────────────────

/// Structural field receiver + additional args: the hint path should handle
/// multi-arg dispatch correctly, encoding the receiver with the expected sort
/// and remaining args normally.
#[test]
#[timeout(30000)]
fn test_tuple_field_receiver_hint_with_extra_args() {
    let mut encoder = AYEncoder::new();

    let custom_sort = Sort::Uninterpreted("MyList".to_string());
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("get_at");
    let decl =
        encoder
            .solver_mut()
            .declare_fun(&smt_name, &[custom_sort.clone(), Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, decl);

    // __trust_wp_tuple_get_1(result).get_at(i)
    let receiver = get_field(1, var("result"));
    let expr = method_call(receiver, "get_at", vec![var("i")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "hint path with extra args should encode: {result:?}"
    );
}

// ── SliceIndexSpec name collision (#knights_tour) ───────────────────

/// A std `usize::in_bounds(seq)` call that was rewritten to a LogicFnCall
/// because a USER logic fn shares the name (e.g. knights_tour's
/// `Board::in_bounds(Board, Point)`) must be rerouted to the builtin
/// SliceIndexSpec semantics instead of being applied to the user declaration
/// through fresh unconstrained coercion constants (which made the negated
/// goal trivially SAT — a false reject).
#[test]
#[timeout(30000)]
fn slice_index_spec_name_collision_reroutes_without_coercion() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new();

    // Register the user's `in_bounds` over non-Int receiver/argument sorts,
    // mirroring knights_tour's `Board::in_bounds(self: Board, p: Point)`.
    let board = Sort::Uninterpreted("Board".to_string());
    let point = Sort::Uninterpreted("Point".to_string());
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("in_bounds");
    let decl = encoder
        .solver_mut()
        .declare_fun(&smt_name, &[board, point], Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, decl);

    // Encode the std-shaped collision call: in_bounds(ix: Int, s: Seq).
    let call = logic_fn_call(
        "in_bounds",
        vec![
            var_with_sort("ix", ExprSort::Int),
            var_with_sort("s", ExprSort::Seq),
        ],
    );
    let baseline = crate::encoder::unsoundness::snapshot();
    let term = encoder
        .encode_pure(&call)
        .expect("collision call should encode via builtin SliceIndexSpec semantics");
    let after = crate::encoder::unsoundness::snapshot();

    // The reroute must produce the inline Bool semantics WITHOUT bridging any
    // argument to a fresh unconstrained constant.
    assert_eq!(
        encoder.solver_mut().get_sort(term),
        Sort::Bool,
        "in_bounds must encode as a Bool predicate"
    );
    let delta = crate::encoder::unsoundness::delta(&baseline, &after);
    assert!(
        !delta.contains_key(&crate::encoder::unsoundness::UnsoundnessCategory::SortCoercionBridge,),
        "collision reroute must not fire the SortCoercionBridge coercion fallback: {delta:?}"
    );
}
