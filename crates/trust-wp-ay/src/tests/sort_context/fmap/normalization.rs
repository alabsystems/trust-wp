// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

/// Test that normalize_sort strips qualified paths from Uninterpreted sorts.
/// `Uninterpreted("std::option::Option")` -> `Uninterpreted("Option")` (#2155)
#[test]
#[timeout(30000)]
fn test_normalize_sort_strips_option_qualified_path_2155() {
    let mut encoder = AYEncoder::new();
    let result = encoder.get_or_declare_var(
        "opt_var",
        Sort::Uninterpreted("std::option::Option".to_string()),
    );
    assert!(result.is_ok());
    assert_eq!(
        encoder.var_sort("opt_var"),
        Some(&Sort::Uninterpreted("Option".to_string())),
        "std::option::Option should be stripped to Option (#2155)"
    );
}

/// Test that normalize_sort strips qualified paths for Result type. (#2155)
#[test]
#[timeout(30000)]
fn test_normalize_sort_strips_result_qualified_path_2155() {
    let mut encoder = AYEncoder::new();
    let result = encoder.get_or_declare_var(
        "res_var",
        Sort::Uninterpreted("std::result::Result".to_string()),
    );
    assert!(result.is_ok());
    assert_eq!(
        encoder.var_sort("res_var"),
        Some(&Sort::Uninterpreted("Result".to_string())),
        "std::result::Result should be stripped to Result (#2155)"
    );
}

/// Test that normalize_sort maps NonNeg to Int. (#2155)
#[test]
#[timeout(30000)]
fn test_normalize_sort_nonneg_to_int_2155() {
    let mut encoder = AYEncoder::new();
    let result = encoder.get_or_declare_var("nn_var", Sort::Uninterpreted("NonNeg".to_string()));
    assert!(result.is_ok());
    assert_eq!(
        encoder.var_sort("nn_var"),
        Some(&Sort::Int),
        "NonNeg should be normalized to Int (#2155)"
    );
}

/// Test that normalize_sort maps RangeInclusive to Int. (#2155)
#[test]
#[timeout(30000)]
fn test_normalize_sort_range_inclusive_to_int_2155() {
    let mut encoder = AYEncoder::new();
    let result = encoder.get_or_declare_var(
        "range_var",
        Sort::Uninterpreted("std::ops::RangeInclusive".to_string()),
    );
    assert!(result.is_ok());
    assert_eq!(
        encoder.var_sort("range_var"),
        Some(&Sort::Int),
        "std::ops::RangeInclusive should be normalized to Int (#2155)"
    );
}

/// Test that infer_expr_sort strips qualified paths for Option Datatype. (#2155)
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_option_strips_path_2155() {
    use trust_wp_core::formula::intern_sort_name;

    let id = intern_sort_name("std::option::Option");
    let expr = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("Option".to_string()),
        "Var with std::option::Option annotation should infer as bare Option (#2155)"
    );
}

/// Test that infer_expr_sort strips qualified paths for Result Datatype. (#2155)
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_result_strips_path_2155() {
    use trust_wp_core::formula::intern_sort_name;

    let id = intern_sort_name("std::result::Result");
    let expr = PureExpr::Var("res".to_string(), Some(ExprSort::Datatype(id)));
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("Result".to_string()),
        "Var with std::result::Result annotation should infer as bare Result (#2155)"
    );
}

/// Test that promote_ambiguous_seqs promotes to FMap when `{name}_view`
/// has FMap evidence. Without this fix, `m.len()` where `m_view` has
/// FMap hint would leave `m` unhinted. (#994)
#[test]
#[timeout(30000)]
fn test_promote_ambiguous_to_fmap_with_view_evidence() {
    let mut encoder = AYEncoder::new();

    // First, register an FMap hint for m_view (e.g., from m@.lookup(k))
    encoder.record_sort_hint("m_view".to_string(), ExprSort::FMap);

    // Build expression with ambiguous method (len) on bare Var m
    let exprs = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("m".to_string(), None)),
        method: "len".to_string(),
        args: vec![],
    }];

    encoder.register_sort_hints(&exprs);

    // `m` should be promoted to FMap (not Seq) since m_view is FMap
    assert_eq!(
        encoder.sort_resolver_for_test().get_sort_hint("m"),
        Some(&ExprSort::FMap),
        "m should be promoted to FMap when m_view has FMap evidence"
    );
}

/// Regression test for #2322: unannotated view-shaped ext_eq operands must
/// seed Seq hints (the default before 1cb7ed45 over-restricted it).
/// Complements `test_ext_eq_on_fmap_views_does_not_promote_seq_hints` above.
#[test]
#[timeout(30000)]
fn test_ext_eq_unannotated_views_seed_seq_hints_2322() {
    // v@.ext_eq(w@) with NO ExprSort annotation — should default to Seq
    let expr = method_call(view(var("v")), "ext_eq", vec![view(var("w"))]);

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&expr, &mut acc);
    assert!(
        acc.seqs.contains("v_view"),
        "unannotated view ext_eq receiver should seed Seq hint, got: {:?}",
        acc.seqs
    );
    assert!(
        acc.seqs.contains("w_view"),
        "unannotated view ext_eq arg should seed Seq hint, got: {:?}",
        acc.seqs
    );

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    assert_eq!(
        encoder.sort_resolver_for_test().get_sort_hint("v_view"),
        Some(&ExprSort::Seq),
        "unannotated view ext_eq receiver hint must become Seq"
    );
    assert_eq!(
        encoder.sort_resolver_for_test().get_sort_hint("w_view"),
        Some(&ExprSort::Seq),
        "unannotated view ext_eq arg hint must become Seq"
    );

    let term = encoder
        .encode_pure(&expr)
        .expect("unannotated view ext_eq should use Seq Tseitin path");
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "ext_eq over unannotated views must produce Bool"
    );
    assert!(
        !encoder.decls().has_logic_func("method_ext_eq_2_s_s"),
        "unannotated view ext_eq should NOT fall back to method_ext_eq UF (#2322)"
    );
}

/// Regression test for #2322: Mapping-annotated ext_eq views must NOT seed Seq.
#[test]
#[timeout(30000)]
fn test_ext_eq_mapping_views_does_not_promote_seq_hints_2322() {
    let expr = method_call(
        view(var_with_sort("m", ExprSort::FMap)),
        "ext_eq",
        vec![view(var_with_sort("n", ExprSort::FMap))],
    );

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&expr, &mut acc);
    assert!(
        !acc.seqs.contains("m_view"),
        "Mapping ext_eq receiver must not seed Seq"
    );
    assert!(
        !acc.seqs.contains("n_view"),
        "Mapping ext_eq arg must not seed Seq"
    );
}
