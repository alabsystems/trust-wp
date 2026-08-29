// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::{
    formula::ExprSort,
    logic::{logic_fn_smt_name, LogicFnDef},
};

use super::*;
mod get_or_declare_var;

// ── get_or_declare_var sort upgrade & conflict paths ─────────────────

// ── Proof coverage: solver.rs untested functions (#904) ──────────────

/// Test `var_sort()` returns correct sort for declared variables.
///
/// Covers: `solver.rs:var_sort()` — previously zero test coverage.
#[test]
#[timeout(30000)]
fn test_var_sort_returns_correct_sort_for_declared_vars() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("int_var", Sort::Int)
        .expect("Int var should declare");
    encoder
        .get_or_declare_var("bool_var", Sort::Bool)
        .expect("Bool var should declare");

    assert_eq!(
        encoder.var_sort("int_var"),
        Some(&Sort::Int),
        "var_sort must return Int for Int-declared variable"
    );
    assert_eq!(
        encoder.var_sort("bool_var"),
        Some(&Sort::Bool),
        "var_sort must return Bool for Bool-declared variable"
    );
    assert_eq!(
        encoder.var_sort("nonexistent"),
        None,
        "var_sort must return None for undeclared variable"
    );
}

/// Test `logic_func_names()` returns registered logic function names.
///
/// Covers: `solver.rs:logic_func_names()` — previously zero test coverage.
#[test]
#[timeout(30000)]
fn test_logic_func_names_returns_registered_functions() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Before registration: empty
    let names_before = encoder.logic_func_names();
    // (may have built-in funcs; test that our registration adds to it)
    let count_before = names_before.len();

    let logic_fn = LogicFnDef::new(
        "test_logic_fn".to_string(),
        "crate::test_logic_fn".to_string(),
        vec!["x".to_string()],
        var("x"),
    );
    encoder
        .register_logic_fn(&logic_fn)
        .expect("logic fn should register");

    let expected_smt_name = logic_fn_smt_name("test_logic_fn");
    let names_after = encoder.logic_func_names();
    assert!(
        names_after.len() > count_before,
        "logic_func_names should include newly registered function"
    );
    assert!(
        names_after.contains(&expected_smt_name),
        "logic_func_names must contain the SMT-encoded name '{expected_smt_name}', got: {names_after:?}"
    );
}

/// Test `spec_func_names()` returns registered spec function names.
///
/// Covers: `solver.rs:spec_func_names()` — previously zero test coverage.
/// Registers a spec function directly via `decls.spec_functions` to guarantee
/// the registration succeeds, avoiding the fragile `encode_pure` path that
/// can silently fail and make the test trivially pass (#1435).
#[test]
#[timeout(30000)]
fn test_spec_func_names_returns_registered_functions() {
    let mut encoder = AYEncoder::new();

    let names_before = encoder.spec_func_names();
    let count_before = names_before.len();

    // Register a spec function directly: declare in the solver, then insert
    // into the decls map (same pattern used by get_or_declare_constructor_tester).
    let decl = encoder
        .solver
        .declare_fun("is_some", &[Sort::Int], Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_spec_func("is_some".to_string(), decl);

    let names_after = encoder.spec_func_names();
    assert!(
        names_after.len() > count_before,
        "spec_func_names should grow after registering a spec function; before={count_before}, after={}",
        names_after.len()
    );
    assert!(
        names_after.contains(&"is_some".to_string()),
        "spec_func_names must contain the registered 'is_some' function, got: {names_after:?}"
    );
}

// ── Proof coverage: sort_context.rs untested functions (#904) ────────

/// Test `sort_from_param_sort()` converts ExprSort to ay Sort correctly.
///
/// Covers: `sort_context.rs:sort_from_param_sort()` — previously `sort_from_param_hint`.
#[test]
#[timeout(30000)]
fn test_sort_from_param_sort_converts_correctly() {
    let mut encoder = AYEncoder::new();

    let bool_sort = encoder.sort_from_param_sort(ExprSort::Bool);
    assert_eq!(
        bool_sort,
        Sort::Bool,
        "ExprSort::Bool must convert to Sort::Bool"
    );

    let seq_sort = encoder.sort_from_param_sort(ExprSort::Seq);
    assert!(
        seq_sort.is_seq(),
        "ExprSort::Seq must convert to Sort::Uninterpreted(\"Seq\"), got: {seq_sort:?}"
    );

    let int_sort = encoder.sort_from_param_sort(ExprSort::Int);
    assert_eq!(
        int_sort,
        Sort::Int,
        "ExprSort::Int must convert to Sort::Int"
    );
}

/// Test `resolve_logic_param_sort()` indirectly by registering a logic function
/// with mixed param sort hints and verifying encoding succeeds.
///
/// Covers: `sort_context.rs:resolve_logic_param_sort()` — previously zero test coverage.
/// Tests the Bool/Seq/default param sort resolution through the public `register_logic_fn` API.
#[test]
#[timeout(30000)]
fn test_resolve_logic_param_sort_via_register_logic_fn() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register a logic function with mixed param sorts:
    // param 0 (a): Bool, param 1 (b): default (Int), param 2 (c): Seq
    let mut logic_fn = LogicFnDef::new(
        "mixed_params".to_string(),
        "crate::mixed_params".to_string(),
        vec!["a".to_string(), "b".to_string(), "c".to_string()],
        var("b"), // body returns Int (param b)
    );
    logic_fn.set_param_sorts(vec![
        Some(ExprSort::Bool), // param 0: Bool
        None,                 // param 1: default (Int)
        Some(ExprSort::Seq),  // param 2: Seq
    ]);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("logic fn with mixed param sorts should register successfully");

    // Verify the function is registered and callable
    let call_expr = logic_fn_call(
        "mixed_params",
        vec![
            bool_expr(true),
            int(42),
            method_call(var("s"), "push_back", vec![int(1)]),
        ],
    );
    let result = encoder.encode_pure(&call_expr);
    assert!(
        result.is_ok(),
        "calling mixed_params with correct-sort args should encode: {result:?}"
    );
}

/// `sort_from_expr_sort(Int)` returns `Sort::Int` (bridge between MIR-level sorts and ay).
#[test]
#[timeout(30000)]
fn test_sort_from_expr_sort_int() {
    let mut encoder = AYEncoder::new();
    let sort = encoder.sort_from_expr_sort(trust_wp_core::formula::ExprSort::Int);
    assert!(
        matches!(sort, Sort::Int),
        "ExprSort::Int must map to Sort::Int, got: {sort:?}"
    );
}

/// `sort_from_expr_sort(Bool)` returns `Sort::Bool`.
#[test]
#[timeout(30000)]
fn test_sort_from_expr_sort_bool() {
    let mut encoder = AYEncoder::new();
    let sort = encoder.sort_from_expr_sort(trust_wp_core::formula::ExprSort::Bool);
    assert!(
        matches!(sort, Sort::Bool),
        "ExprSort::Bool must map to Sort::Bool, got: {sort:?}"
    );
}

/// `sort_from_expr_sort(Unit)` returns `Sort::Uninterpreted("Unit")`.
///
/// Aligned with `expr_sort_to_ay_sort` to prevent dual-path sort disagreements
/// where declaration sorts (via `sort_from_expr_sort`) and usage sorts (via
/// `infer_expr_sort`/`expr_sort_to_ay_sort`) would produce different ay sorts
/// for the same ExprSort variant. (#2059)
#[test]
#[timeout(30000)]
fn test_sort_from_expr_sort_unit_maps_to_uninterpreted() {
    let mut encoder = AYEncoder::new();
    let sort = encoder.sort_from_expr_sort(trust_wp_core::formula::ExprSort::Unit);
    assert_eq!(
        sort,
        Sort::Uninterpreted("Unit".to_string()),
        "ExprSort::Unit must map to Uninterpreted(Unit), consistent with expr_sort_to_ay_sort"
    );
}

/// `sort_from_expr_sort(Seq)` returns a Seq sort without eagerly initializing
/// the Seq theory table.
///
/// Seq theory declarations are now created on first Seq-theory use, not during
/// pure sort resolution. Encoding a Seq operation must still initialize the
/// theory on demand.
#[test]
#[timeout(30000)]
fn test_sort_from_expr_sort_seq_keeps_theory_lazy_then_encodes_len() {
    let mut encoder = AYEncoder::new();
    let sort = encoder.sort_from_expr_sort(trust_wp_core::formula::ExprSort::Seq);

    // The sort should be native Sort::Seq(Int) (#2080)
    assert!(
        sort.is_seq(),
        "ExprSort::Seq must map to Sort::Seq(Int), got: {sort:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "sort_from_expr_sort(Seq) should not initialize the Seq theory table"
    );

    // Encoding a Seq operation should initialize the theory on demand.
    let seq_len = method_call(
        PureExpr::Var("s".to_string(), Some(ExprSort::Seq)),
        "len",
        vec![],
    );
    let result = encoder.encode_pure(&seq_len);
    assert!(
        result.is_ok(),
        "encoding a Seq operation after sort_from_expr_sort(Seq) should still succeed: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "encoding a Seq operation should initialize the Seq theory table on demand"
    );
}

/// `sort_from_expr_sort(Ref(Seq))` peels the `Ref` and still keeps the Seq
/// theory lazy.
///
/// The wrapped sort must resolve to `Seq`, but theory declarations should wait
/// until an actual Seq operation is encoded. (#1965 Phase 2 audit, #1565)
#[test]
#[timeout(30000)]
fn test_sort_from_expr_sort_ref_seq_keeps_theory_lazy_then_encodes_len() {
    let mut encoder = AYEncoder::new();
    let sort = encoder.sort_from_expr_sort(trust_wp_core::formula::ExprSort::Ref(Box::new(
        trust_wp_core::formula::ExprSort::Seq,
    )));

    // Ref(Seq) peels to Seq sort (logical level ignores reference wrappers).
    assert!(
        sort.is_seq(),
        "ExprSort::Ref(Seq) must map to Sort::Uninterpreted(\"Seq\"), got: {sort:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "sort_from_expr_sort(Ref(Seq)) should not initialize the Seq theory table"
    );

    // Encoding a Seq operation should still initialize the theory on demand.
    let seq_len = method_call(
        PureExpr::Var(
            "s".to_string(),
            Some(ExprSort::Ref(Box::new(ExprSort::Seq))),
        ),
        "len",
        vec![],
    );
    let result = encoder.encode_pure(&seq_len);
    assert!(
        result.is_ok(),
        "encoding a Seq operation after sort_from_expr_sort(Ref(Seq)) should still succeed: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "encoding a Seq operation should initialize the Seq theory table on demand"
    );
}

/// Regression: resolve_decl_sort must prefer Seq hint over base_name's
/// default Int sort. Mut-borrow alias setup declares base variables as Int
/// (via `infer_expr_sort` default), which caused view variables to inherit
/// Int sort even when the prescan registered a Seq hint — leading to
/// `seq_array: Sort mismatch` panics when `.tail()` was called. (#1805)
#[test]
#[timeout(30000)]
fn test_resolve_decl_sort_seq_hint_overrides_base_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Simulate mut-borrow alias setup: declare base variable as Int (default).
    encoder
        .get_or_declare_var("self__current_current", Sort::Int)
        .expect("declare base var");

    // Register Seq hint for the view variable (as prescan would).
    encoder.record_sort_hint(
        "self__current_current_view".to_string(),
        trust_wp_core::formula::ExprSort::Seq,
    );

    // Build: View(Deref(Deref(Var("self_")))) == View(Deref(Deref(Var("self_")))).tail()
    let view_self_cc = view(deref(deref(var("self_"))));
    let tail_call = method_call(view_self_cc.clone(), "tail", vec![]);
    let eq_expr = eq(view_self_cc, tail_call);

    // Sort hints for the equality
    encoder.register_sort_hints(std::slice::from_ref(&eq_expr));

    // Encode — should NOT panic with sort mismatch.
    let result = encoder.encode_pure(&eq_expr);
    assert!(
        result.is_ok(),
        "View variable with Seq hint should not inherit base Int sort: {result:?} (#1805)"
    );
}

/// Regression: resolve_decl_sort must also respect a non-Int fallback when the
/// base variable is already declared Int.
///
/// Pattern: `old(s_seq)` where `s` was predeclared as Int by another path.
/// The prefixed variable `old_s` should keep the explicit Seq fallback from
/// the sort annotation, not inherit Int from `s`. (#1805)
#[test]
#[timeout(30000)]
fn test_resolve_decl_sort_fallback_seq_overrides_base_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("s", Sort::Int)
        .expect("declare base var as Int");

    let expr = old(var_with_sort("s", ExprSort::Seq));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "old(seq-annotated var) should encode without inheriting base Int sort: {result:?}"
    );

    let old_sort = encoder.var_sort("old_s");
    assert!(
        old_sort.is_some_and(ay_dpll::ApiSort::is_seq),
        "old_s should be Seq-sorted from explicit fallback, got: {old_sort:?}"
    );
}

/// Regression: a direct hint on a derived view name must beat the base
/// variable's non-Int carrier sort.
///
/// Iterator snapshots like `call_2: IterMut` can still have collection views
/// `call_2_view: FMap`. When `resolve_decl_sort("call_2_view", Some("call_2"), ..)`
/// prefers the base non-Int sort first, `call_2_view` is incorrectly declared
/// as `IterMut`, and later `call_2@.contains(k)` crashes in `fmap_contains`.
/// (#994)
#[test]
#[timeout(30000)]
fn test_encode_view_uses_direct_fmap_hint_over_base_iterator_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    encoder
        .get_or_declare_var("call_2", Sort::Uninterpreted("IterMut".to_string()))
        .expect("declare iterator snapshot");
    encoder.record_sort_hint(
        "call_2_view".to_string(),
        trust_wp_core::formula::ExprSort::FMap,
    );

    let result = encoder.encode_pure(&view(var("call_2")));
    assert!(
        result.is_ok(),
        "view variable should honor direct FMap hint over base IterMut sort: {result:?}"
    );
    assert_eq!(
        encoder.var_sort("call_2_view"),
        Some(&Sort::Uninterpreted("FMap".to_string())),
        "call_2_view should be declared as FMap, not inherit IterMut"
    );
}

// ── Algorithm audit: sort resolution boundary conditions (#1948) ─────

/// Algorithm audit: resolve_var_sort_or_int returns Seq when base has Seq
/// hint but is declared as Int.
///
/// Tests the resolve chain: when "s" is declared Int but has a Seq hint,
/// the hint should override the weak Int declaration. (#1948 algorithm audit)
#[test]
#[timeout(30000)]
fn test_resolve_sort_base_seq_hint_discoverable_through_resolve() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Base "s" declared as Int (default), with a Seq hint registered.
    encoder
        .get_or_declare_var("s", Sort::Int)
        .expect("declare base as Int");
    encoder.record_sort_hint("s".to_string(), trust_wp_core::formula::ExprSort::Seq);

    // resolve_var_sort_or_int("s") should find the Seq hint even though
    // the var_sort is Int — hints override default-Int declarations.
    let sort = encoder.resolve_var_sort_or_int("s");
    assert!(
        sort.is_seq(),
        "Seq hint on 's' should override declared Int sort; got {sort:?}"
    );
}

/// Algorithm audit: resolve_var_sort_or_int prefers non-Int declared sort
/// over any hint.
///
/// When a variable is declared with a non-Int sort (e.g., Bool from a
/// match path), that sort should take priority over any registered hint.
#[test]
#[timeout(30000)]
fn test_resolve_sort_declared_non_int_beats_hint() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    encoder
        .get_or_declare_var("flag", Sort::Bool)
        .expect("declare flag as Bool");
    // Register a conflicting Seq hint — should NOT override Bool.
    encoder.record_sort_hint("flag".to_string(), trust_wp_core::formula::ExprSort::Seq);

    let sort = encoder.resolve_var_sort_or_int("flag");
    assert_eq!(
        sort,
        Sort::Bool,
        "Declared Bool sort must beat Seq hint; got {sort:?}"
    );
}

/// Algorithm audit: record_sort_hint protects Seq from Bool overwrite.
///
/// Seq and FMap hints are more specific than Bool (#1517, #1778).
/// A subsequent Bool hint must not overwrite an existing Seq hint.
#[test]
#[timeout(30000)]
fn test_record_sort_hint_seq_protected_from_bool() {
    let mut encoder = AYEncoder::new();

    encoder.record_sort_hint("x".to_string(), trust_wp_core::formula::ExprSort::Seq);
    encoder.record_sort_hint("x".to_string(), trust_wp_core::formula::ExprSort::Bool);

    // Seq should be preserved — Bool cannot overwrite Seq.
    assert!(
        encoder.is_seq_receiver(&var("x"), None),
        "Seq hint on 'x' must survive Bool overwrite attempt"
    );
}

/// Algorithm audit: record_sort_hint allows Seq to overwrite FMap.
///
/// FMap hints survive Seq override attempts. The prescan's ambiguous-method
/// heuristic tags non-Var receivers of `len`/`contains`/`get` as Seq by
/// default. When FMap evidence already exists, the weaker Seq heuristic
/// must not override it. Without this priority, `collections` receivers
/// with FMap hints get misclassified as Seq. (#994 RC2)
#[test]
#[timeout(30000)]
fn test_record_sort_hint_fmap_survives_seq_override() {
    let mut encoder = AYEncoder::new();

    encoder.record_sort_hint("m".to_string(), trust_wp_core::formula::ExprSort::FMap);
    encoder.record_sort_hint("m".to_string(), trust_wp_core::formula::ExprSort::Seq);

    assert!(
        encoder.is_fmap_receiver(&var("m"), None),
        "FMap hint must survive Seq override; 'm' should remain FMap"
    );
    assert!(
        !encoder.is_seq_receiver(&var("m"), None),
        "FMap hint must NOT be overwritten by Seq"
    );
}

/// Algorithm audit: fixpoint propagation handles two-hop chain.
///
/// The fixpoint loop in register_sort_hints propagates:
///   `final_x_view` → `x_view` → `x`
/// This two-hop chain requires two iterations. Verify fixpoint convergence.
///
/// We use a Seq method call (len) on View(Final(Var("x"))) so the prescan
/// collector adds "final_x_view" to acc.seqs, triggering propagation.
#[test]
#[timeout(30000)]
fn test_fixpoint_propagation_two_hop_chain() {
    let mut encoder = AYEncoder::new();

    // View(Final(Var("x"))).len() — "len" is an ambiguous-seq method on a
    // non-Var receiver, so the prescan adds "final_x_view" to acc.seqs.
    let view_final_x = view(final_expr(var("x")));
    let len_call = method_call(view_final_x, "len", vec![]);
    encoder.register_sort_hints(std::slice::from_ref(&len_call));

    // After fixpoint propagation:
    //   final_x_view → x_view (strip final_ prefix, re-add _view)
    //   x_view → x (strip _view suffix)
    assert!(
        encoder.is_seq_receiver(&var("x"), None),
        "fixpoint must propagate final_x_view → x_view → x as Seq"
    );
}

/// Algorithm audit: fixpoint propagation skips `_current` suffix names
/// in the sort_hints map.
///
/// The `_current` guard in the `_view → base` rule prevents tagging
/// `self__current` as Seq when `self__current_view` is collected.
/// This is critical for mut-borrow correctness (#1948).
///
/// NOTE: `is_seq_receiver` has a secondary path that normalizes bare Var
/// receivers into View(...) form, which bypasses this guard. The guard
/// only protects the sort_hints map entry for the raw name. The sort
/// resolution functions (`resolve_var_sort_or_int`) check sort_hints
/// directly, so the guard is effective there.
#[test]
#[timeout(30000)]
fn test_fixpoint_propagation_skips_current_suffix_in_hints() {
    let mut encoder = AYEncoder::new();

    // View(Deref(Var("self_"))).len() — resolve_view_var_name resolves
    // the Deref to _current naming: "self__current_view". The len method
    // on a non-Var receiver triggers the ambiguous-seq path.
    let view_deref_self = view(deref(var("self_")));
    let len_call = method_call(view_deref_self, "len", vec![]);
    encoder.register_sort_hints(std::slice::from_ref(&len_call));

    // "self__current" should NOT have a direct Seq hint in sort_hints.
    // The fixpoint sees "self__current_view", strips _view → "self__current",
    // but base.ends_with("_current") is true, so propagation is blocked.
    assert!(
        !encoder.is_bool_var("self__current"),
        "self__current should not be Bool-hinted (sanity check)"
    );
    // Check that resolve_var_sort_or_int does NOT return Seq for the raw name.
    // The _current guard prevents "self__current" from getting a Seq hint,
    // so only suffix-stripping (→ "self_") could resolve it, and "self_"
    // has no sort hint either.
    let sort = encoder.resolve_var_sort_or_int("self__current");
    assert_eq!(
        sort,
        Sort::Int,
        "self__current must resolve to Int (not Seq) — _current guard blocks propagation (#1948)"
    );
}

/// Algorithm audit: resolve_var_sort_candidate strips multiple suffixes.
///
/// A name like `x_current_final` should resolve by stripping `_final`
/// first (getting `x_current`), then `_current` (getting `x`).
#[test]
#[timeout(30000)]
fn test_resolve_var_sort_candidate_multi_suffix_stripping() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare base variable "x" as Bool.
    encoder
        .get_or_declare_var("x", Sort::Bool)
        .expect("declare x as Bool");

    // "x_current_final" has no direct declaration or hint.
    // resolve_var_sort_or_int should strip _final → x_current,
    // then _current → x, finding Bool.
    let sort = encoder.resolve_var_sort_or_int("x_current_final");
    assert_eq!(
        sort,
        Sort::Bool,
        "x_current_final should resolve to x's Bool sort via suffix stripping"
    );
}

/// Algorithm audit: resolve_var_sort_or_int strips old_ prefix then suffixes.
///
/// Name: `old_v_current` → strip old_ → `v_current` → strip _current → `v`.
#[test]
#[timeout(30000)]
fn test_resolve_var_sort_or_int_old_prefix_then_suffix() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    encoder
        .get_or_declare_var("v", Sort::Bool)
        .expect("declare v as Bool");

    let sort = encoder.resolve_var_sort_or_int("old_v_current");
    assert_eq!(
        sort,
        Sort::Bool,
        "old_v_current should resolve via old_ strip → v_current → suffix strip → v (Bool)"
    );
}

// ── resolve_var_sort_or_int_with_annotation: non-None annotation paths (#2078) ──

/// Annotation path: Bool annotation overrides default Int when cascade finds nothing.
///
/// When the hint cascade finds no candidate at all, a Bool annotation
/// should serve as fallback, returning Sort::Bool instead of Sort::Int.
#[test]
#[timeout(30000)]
fn test_annotation_bool_overrides_weak_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // No hints or declarations for "flag" — cascade finds no candidate.
    let sort = encoder.resolve_var_sort_or_int_with_annotation("flag", Some(&ExprSort::Bool));
    assert_eq!(
        sort,
        Sort::Bool,
        "Bool annotation should override default Int fallback"
    );
}

/// Annotation path: Seq annotation overrides default Int when cascade finds nothing.
///
/// Same as Bool test but for Seq: the annotation should produce
/// Sort::Seq(Int) instead of Int. (#2078, #2080)
#[test]
#[timeout(30000)]
fn test_annotation_seq_overrides_weak_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let sort = encoder.resolve_var_sort_or_int_with_annotation("items", Some(&ExprSort::Seq));
    assert!(
        sort.is_seq(),
        "Seq annotation should produce Sort::Seq(Int); got {sort:?}"
    );
}

/// Annotation path: FMap annotation triggers early return (high-confidence).
///
/// FMap is in the early-return set (Datatype/FMap/Tuple). It should bypass
/// the hint cascade entirely and return immediately. (#2078)
#[test]
#[timeout(30000)]
fn test_annotation_fmap_early_return() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Even with a conflicting Bool declaration, FMap annotation wins.
    encoder
        .get_or_declare_var("m", Sort::Bool)
        .expect("declare m as Bool");

    let sort = encoder.resolve_var_sort_or_int_with_annotation("m", Some(&ExprSort::FMap));
    assert!(
        matches!(&sort, Sort::Uninterpreted(name) if name == "FMap"),
        "FMap annotation should early-return Uninterpreted(\"FMap\"); got {sort:?}"
    );
}

/// Annotation path: Tuple(2) annotation triggers early return.
///
/// Tuple is in the early-return set. Should produce Uninterpreted("Tuple2").
#[test]
#[timeout(30000)]
fn test_annotation_tuple_early_return() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let sort = encoder.resolve_var_sort_or_int_with_annotation("pair", Some(&ExprSort::Tuple(2)));
    assert!(
        matches!(&sort, Sort::Uninterpreted(name) if name == "Tuple2"),
        "Tuple(2) annotation should produce Uninterpreted(\"Tuple2\"); got {sort:?}"
    );
}

/// Annotation path: Datatype annotation triggers early return.
///
/// When a Datatype annotation is provided, it should bypass the hint cascade
/// and return immediately with the interned sort name. (#2078)
#[test]
#[timeout(30000)]
fn test_annotation_datatype_early_return() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    let id = intern_sort_name("Option");
    let sort =
        encoder.resolve_var_sort_or_int_with_annotation("opt", Some(&ExprSort::Datatype(id)));
    // No declared datatype → falls through to Uninterpreted("Option")
    assert!(
        matches!(&sort, Sort::Uninterpreted(name) if name == "Option"),
        "Datatype(Option) annotation should produce Uninterpreted(\"Option\"); got {sort:?}"
    );
}

/// Annotation path: Ref(Datatype) peels the Ref and triggers early return.
///
/// The function peels Ref layers to find inner structured sorts. A
/// Ref(Datatype) should behave the same as bare Datatype for the
/// early-return check. (#2078, #2040)
///
/// Vec is a Seq-model collection type, so Ref(Datatype(Vec)) routes
/// through the is_seq_model_type check and produces Seq sort. (#2124 Phase 4b)
#[test]
#[timeout(30000)]
fn test_annotation_ref_datatype_peeled() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    let id = intern_sort_name("Vec");
    let ann = ExprSort::Ref(Box::new(ExprSort::Datatype(id)));
    let sort = encoder.resolve_var_sort_or_int_with_annotation("v", Some(&ann));
    // Vec is a Seq-model collection type (#2124 Phase 4b): the Ref layer is
    // peeled, then the Datatype arm detects Vec as a collection whose deep
    // model is Seq, routing it to the Seq sort.
    assert!(
        sort.is_seq(),
        "Ref(Datatype(Vec)) should produce Seq sort; got {sort:?}"
    );
}

/// Annotation path: Datatype("creusot_std::Seq") maps to Seq sort.
///
/// Creusot's own `creusot_std::Seq<T>` type IS the logical sequence type.
/// When the driver produces `Datatype("creusot_std::Seq")`, `is_seq_model_type`
/// matches `"Seq"` (the unqualified name) and routes to the canonical Seq sort.
/// Without this, `creusot_std::Seq` gets `Uninterpreted("creusot_std::Seq")`
/// which causes sort mismatches in seq_len/seq_array calls. (#2155)
#[test]
#[timeout(30000)]
fn test_annotation_creusot_seq_datatype_maps_to_seq() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    let id = intern_sort_name("creusot_std::Seq");
    let ann = ExprSort::Datatype(id);
    let sort = encoder.resolve_var_sort_or_int_with_annotation("s", Some(&ann));
    assert!(
        sort.is_seq(),
        "Datatype(creusot_std::Seq) should produce Seq sort; got {sort:?}"
    );
}

/// Annotation path: Ref(Datatype) for a non-collection type peels to
/// Uninterpreted. This confirms that Ref-peeling still works for
/// non-Seq datatypes after the is_seq_model_type routing. (#2078, #2124)
#[test]
#[timeout(30000)]
fn test_annotation_ref_non_collection_datatype_peeled() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    let id = intern_sort_name("MyStruct");
    let ann = ExprSort::Ref(Box::new(ExprSort::Datatype(id)));
    let sort = encoder.resolve_var_sort_or_int_with_annotation("v", Some(&ann));
    // Non-collection datatypes bypass the Seq routing and produce
    // Uninterpreted with the original type name.
    assert!(
        matches!(&sort, Sort::Uninterpreted(name) if name == "MyStruct"),
        "Ref(Datatype(MyStruct)) should produce Uninterpreted(\"MyStruct\"); got {sort:?}"
    );
}

/// Annotation path: Unit annotation overrides default Int when cascade finds nothing.
///
/// Unit is not in the early-return set (Datatype/FMap/Tuple) so it acts as
/// a fallback. Should produce Uninterpreted("Unit"). (#2078)
#[test]
#[timeout(30000)]
fn test_annotation_unit_overrides_weak_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let sort = encoder.resolve_var_sort_or_int_with_annotation("u", Some(&ExprSort::Unit));
    assert!(
        matches!(&sort, Sort::Uninterpreted(name) if name == "Unit"),
        "Unit annotation should produce Uninterpreted(\"Unit\"); got {sort:?}"
    );
}

/// Annotation path: Bool annotation overrides explicit Int cascade result.
///
/// When the cascade finds a candidate that IS Int (variable declared as Int),
/// the non-Int Bool annotation is authoritative and bypasses it. Under Phase 2
/// (#1965), annotations short-circuit the cascade when non-Int. (#2078)
#[test]
#[timeout(30000)]
fn test_annotation_bool_overrides_explicit_weak_int_cascade() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare "count" as Int — cascade will find Some(Int) (weak result).
    encoder
        .get_or_declare_var("count", Sort::Int)
        .expect("declare count as Int");

    // Bool annotation should override the weak Int cascade result.
    let sort = encoder.resolve_var_sort_or_int_with_annotation("count", Some(&ExprSort::Bool));
    assert_eq!(
        sort,
        Sort::Bool,
        "Bool annotation should override explicit weak-Int cascade; got {sort:?}"
    );
}

/// Annotation path: non-Int annotation is authoritative (Phase 2, #1965).
///
/// When a non-Int ExprSort annotation is provided, it is authoritative and
/// bypasses the entire heuristic hint cascade, even when the cascade would
/// find a non-Int sort. MIR-derived type information is more reliable than
/// string-based heuristics.
#[test]
#[timeout(30000)]
fn test_annotation_is_authoritative_over_cascade() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare "x" as Bool — the cascade would find this non-Int sort.
    encoder
        .get_or_declare_var("x", Sort::Bool)
        .expect("declare x as Bool");

    // Provide a Seq annotation — annotation is authoritative in Phase 2.
    let sort = encoder.resolve_var_sort_or_int_with_annotation("x", Some(&ExprSort::Seq));
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "Non-Int Seq annotation should be authoritative over Bool cascade; got {sort:?}"
    );
}

// ── encode_pure end-to-end: Var annotation → ay variable sort (#2078) ──────

/// End-to-end test: PureExpr::Var with Datatype annotation produces
/// the correct ay variable sort after passing through encode_pure.
///
/// This verifies that the annotation wiring in pure_encoding.rs Var arm
/// (line 170) actually threads the ExprSort through to
/// resolve_var_sort_or_int_with_annotation and that the resulting ay
/// variable is declared with the Datatype sort, not the default Int.
///
/// Without annotation, the same variable name would resolve to Int (no
/// hints, no declarations). With annotation, it resolves to
/// Uninterpreted("Option"). (#2078)
#[test]
#[timeout(30000)]
fn test_encode_pure_var_datatype_annotation_produces_correct_sort() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();

    let id = intern_sort_name("Option");

    // Var with no annotation → default Int
    let no_ann = var("opt_none");
    let result_none = encoder.encode_pure(&no_ann);
    assert!(
        result_none.is_ok(),
        "encode_pure(Var without annotation) should succeed"
    );
    assert_eq!(
        encoder.var_sorts_for_test().get("opt_none"),
        Some(&Sort::Int),
        "Var without annotation should default to Int"
    );

    // Var with Datatype annotation → Uninterpreted("Option")
    let with_ann = var_with_sort("opt_typed", ExprSort::Datatype(id));
    let result_typed = encoder.encode_pure(&with_ann);
    assert!(
        result_typed.is_ok(),
        "encode_pure(Var with Datatype annotation) should succeed"
    );
    let declared_sort = encoder
        .var_sorts_for_test()
        .get("opt_typed")
        .expect("opt_typed should be declared after encode_pure");
    assert!(
        matches!(declared_sort, Sort::Uninterpreted(name) if name == "Option"),
        "Datatype(Option) annotation should produce Uninterpreted(\"Option\"), got {declared_sort:?}"
    );
}

/// End-to-end test: PureExpr::Var with FMap annotation produces
/// Uninterpreted("FMap") after encode_pure, not the default Int.
///
/// FMap is in the early-return tier (Datatype/FMap/Tuple), so it
/// bypasses the hint cascade entirely. (#2078)
#[test]
#[timeout(30000)]
fn test_encode_pure_var_fmap_annotation_produces_correct_sort() {
    let mut encoder = AYEncoder::new();

    let expr = var_with_sort("mapping", ExprSort::FMap);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "encode_pure(Var with FMap annotation) should succeed"
    );
    let declared_sort = encoder
        .var_sorts_for_test()
        .get("mapping")
        .expect("mapping should be declared after encode_pure");
    assert!(
        matches!(declared_sort, Sort::Uninterpreted(name) if name == "FMap"),
        "FMap annotation should produce Uninterpreted(\"FMap\"), got {declared_sort:?}"
    );
}

/// End-to-end test: PureExpr::Var with Bool annotation falls back
/// to Sort::Bool instead of Int when no hints exist.
///
/// Bool is in the fallback tier (not early-return), so the hint cascade
/// runs first. With no hints, the annotation serves as the fallback. (#2078)
#[test]
#[timeout(30000)]
fn test_encode_pure_var_bool_annotation_overrides_default_int() {
    let mut encoder = AYEncoder::new();

    let expr = var_with_sort("flag", ExprSort::Bool);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "encode_pure(Var with Bool annotation) should succeed"
    );
    assert_eq!(
        encoder.var_sorts_for_test().get("flag"),
        Some(&Sort::Bool),
        "Bool annotation should produce Sort::Bool, not default Int"
    );
}

// ── resolve_logic_param_sort: silent Int fallback (soundness gap) ──────

/// Strategic audit: `resolve_logic_param_sort` silently returns `Sort::Int`
/// when no `param_sorts` annotation AND no sort hint exist for a parameter.
///
/// **Soundness implication:** If a logic function takes a Bool parameter but
/// the driver omits `param_sorts` (e.g., user-defined `#[logic]` without type
/// annotations), the function is declared with Int parameter sort. Combined
/// with `SortFallbackToIntFromVar` (non-demoting) on the argument side, a
/// resolve_logic_param_sort with no annotation/hint falls back to Int and
/// now fires an unsoundness counter so demote_if_unsound can catch false
/// proofs caused by Bool-as-Int parameter sort mismatches (#2352).
///
/// Part of #2231 (Sort::Int systemic debt), fixed by #2362.
#[test]
#[timeout(30000)]
fn test_resolve_logic_param_sort_no_annotation_no_hint_returns_int_with_counter() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    unsoundness::reset();
    let before = unsoundness::snapshot();

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Create a logic function with NO param_sorts annotations.
    // Parameter "flag" is conceptually Bool, but has no annotation.
    let logic_fn = LogicFnDef::new(
        "check_flag".to_string(),
        "crate::check_flag".to_string(),
        vec!["flag".to_string()],
        var("flag"), // body: returns the parameter
    );
    // No set_param_sorts call — simulates missing type info from driver.

    // resolve_logic_param_sort should return Int (no annotation, no hint).
    let sort = encoder.resolve_logic_param_sort(&logic_fn, 0);
    assert_eq!(
        sort,
        Sort::Int,
        "resolve_logic_param_sort with no annotation/hint should return Int"
    );

    // Counter must now fire for the Int fallback (#2352).
    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert!(
        delta.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn) == Some(&1),
        "resolve_logic_param_sort Int fallback must increment SortFallbackToIntFromLogicFn (#2002, #2352). Delta: {delta:?}"
    );

    unsoundness::reset();
}

/// Preseeded declaration-side variable sorts must participate in logic
/// parameter sort resolution before the final Int fallback. (#2002)
#[test]
#[timeout(30000)]
fn test_resolve_logic_param_sort_uses_preseeded_var_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .var_sorts_mut_for_test()
        .insert("xs".to_string(), Sort::seq(Sort::Int));

    let logic_fn = LogicFnDef::new(
        "forward_seq".to_string(),
        "crate::forward_seq".to_string(),
        vec!["xs".to_string()],
        int(0),
    );

    let sort = encoder.resolve_logic_param_sort(&logic_fn, 0);
    assert!(
        sort.is_seq(),
        "preseeded non-Int var_sorts must override Int fallback, got: {sort:?}"
    );
}

/// Logic function declared with no param_sorts annotation now fires an
/// unsoundness counter via resolve_logic_param_sort (#2352).
///
/// Previously, both the declaration (param sort) and call site (argument sort)
/// silently defaulted to Int. Now SortFallbackToIntFromLogicFn fires for the
/// parameter declaration fallback, so demote_if_unsound can catch false proofs.
///
/// Part of #2231 (Sort::Int systemic debt), fixed by #2362.
#[test]
#[timeout(30000)]
fn test_logic_fn_bool_param_no_annotation_fires_param_sort_counter() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    unsoundness::reset();
    let before = unsoundness::snapshot();

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Logic function: check_flag(flag) = flag
    // Conceptually Bool-typed, but no param_sorts annotation.
    let logic_fn = LogicFnDef::new(
        "check_flag2".to_string(),
        "crate::check_flag2".to_string(),
        vec!["flag".to_string()],
        var("flag"),
    );

    // Register the function — declaration uses Int for the parameter.
    let reg_result = encoder.register_logic_fn(&logic_fn);
    assert!(
        reg_result.is_ok(),
        "register_logic_fn should succeed: {reg_result:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);

    // SortFallbackToIntFromLogicFn now fires for the parameter sort fallback.
    let has_sort_fallback = delta
        .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
        .copied()
        .unwrap_or(0)
        > 0;
    assert!(
        has_sort_fallback,
        "resolve_logic_param_sort Int fallback must fire SortFallbackToIntFromLogicFn (#2002, #2352). \
         Delta: {delta:?}"
    );

    // Verify the function was declared with Int (not Bool) param sort.
    let smt_name = logic_fn_smt_name("check_flag2");
    let func_decl = encoder.decls().get_logic_func(&smt_name);
    assert!(
        func_decl.is_some(),
        "check_flag2 should be registered in decls"
    );
    if let Some(decl) = func_decl {
        let domain = decl.domain();
        assert!(
            !domain.is_empty(),
            "check_flag2 should have at least one parameter"
        );
        assert_eq!(
            domain[0],
            Sort::Int,
            "Parameter sort should be Int (silent fallback), not Bool. \
             This is the documented gap: Bool parameters without annotations \
             are declared as Int with no demotion tracking."
        );
    }

    unsoundness::reset();
}
