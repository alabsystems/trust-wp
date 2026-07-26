// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_logic_fn_smt_name_simple() {
    assert_eq!(logic_fn_smt_name("max"), "logic_max");
    assert_eq!(logic_fn_smt_name("min"), "logic_min");
}

#[test]
fn test_logic_fn_smt_name_qualified() {
    assert_eq!(
        logic_fn_smt_name("crate::specs::max"),
        "logic_crate_P__P_specs_P__P_max"
    );
    assert_eq!(
        logic_fn_smt_name("foo::bar::baz"),
        "logic_foo_P__P_bar_P__P_baz"
    );
}

#[test]
fn test_logic_fn_smt_name_empty() {
    assert_eq!(logic_fn_smt_name(""), "logic_");
}

#[test]
fn test_logic_fn_smt_name_injective() {
    // #1435: foo_bar and foo::bar must produce distinct SMT names
    assert_ne!(logic_fn_smt_name("foo_bar"), logic_fn_smt_name("foo::bar"));
    // Verify the actual values
    assert_eq!(logic_fn_smt_name("foo_bar"), "logic_foo__bar");
    assert_eq!(logic_fn_smt_name("foo::bar"), "logic_foo_P__P_bar");
}

#[test]
fn test_logic_fn_smt_name_special_chars() {
    // Generic types
    assert_eq!(logic_fn_smt_name("Vec<T>"), "logic_Vec_LT_T_GT_");
    // Underscore escaping is injective
    assert_ne!(logic_fn_smt_name("a_LT_b"), logic_fn_smt_name("a<b"));
}

#[test]
fn test_logic_mode_from_marker_suffix_default() {
    assert_eq!(LogicMode::from_marker_suffix(""), LogicMode::Default);
}

#[test]
fn test_logic_mode_from_marker_suffix_open() {
    assert_eq!(LogicMode::from_marker_suffix("open:"), LogicMode::Open);
}

#[test]
fn test_logic_mode_from_marker_suffix_open_self() {
    assert_eq!(
        LogicMode::from_marker_suffix("open_self:"),
        LogicMode::OpenSelf
    );
}

#[test]
fn test_logic_mode_from_marker_suffix_prophetic() {
    assert_eq!(
        LogicMode::from_marker_suffix("prophetic:"),
        LogicMode::Prophetic
    );
}

#[test]
fn test_logic_mode_from_marker_suffix_predicate() {
    // "predicate" suffix indicates predicate type, not a mode
    assert_eq!(
        LogicMode::from_marker_suffix("predicate"),
        LogicMode::Default
    );
}

#[test]
fn test_logic_mode_from_marker_suffix_open_predicate() {
    assert_eq!(
        LogicMode::from_marker_suffix("open:predicate"),
        LogicMode::Open
    );
}

#[test]
fn test_logic_mode_from_marker_suffix_prophetic_predicate() {
    assert_eq!(
        LogicMode::from_marker_suffix("prophetic:predicate"),
        LogicMode::Prophetic
    );
}

#[test]
fn test_logic_mode_try_from_marker_suffix_rejects_unknown() {
    assert!(
        LogicMode::try_from_marker_suffix("opn:").is_none(),
        "typo 'opn' should not silently parse as a valid mode"
    );
    assert!(
        LogicMode::try_from_marker_suffix("open_slef:").is_none(),
        "typo 'open_slef' should not silently parse as a valid mode"
    );
    assert!(
        LogicMode::try_from_marker_suffix("bogus:").is_none(),
        "unknown mode 'bogus' should return None"
    );
    // from_marker_suffix still falls back to Default for backwards compat
    assert_eq!(LogicMode::from_marker_suffix("opn:"), LogicMode::Default);
}

#[test]
fn test_param_sort_hint_into_expr_sort() {
    assert_eq!(ExprSort::from(ParamSortHint::Bool), ExprSort::Bool);
    assert_eq!(ExprSort::from(ParamSortHint::Seq), ExprSort::Seq);
}

#[test]
fn test_param_sort_hint_datatype_into_expr_sort() {
    let hint = ParamSortHint::Datatype("OptionInt".to_string());
    let sort = ExprSort::from(hint);
    // ExprSort::Datatype uses an interned u32 id; verify round-trip via resolve.
    match sort {
        ExprSort::Datatype(id) => {
            assert_eq!(
                crate::formula::resolve_sort_name(id),
                "OptionInt",
                "Datatype hint must intern the name correctly"
            );
        }
        other => panic!("expected ExprSort::Datatype, got {other:?}"),
    }
}

#[test]
fn test_param_sort_hint_resolve_expr_sort_default_int() {
    assert_eq!(
        ParamSortHint::resolve_expr_sort(None),
        ExprSort::Int,
        "None param sort hint must resolve to Int default"
    );
    assert_eq!(
        ParamSortHint::resolve_expr_sort(Some(ParamSortHint::Bool)),
        ExprSort::Bool
    );
    assert_eq!(
        ParamSortHint::resolve_expr_sort(Some(ParamSortHint::Seq)),
        ExprSort::Seq
    );
}

#[test]
fn test_param_sort_hint_resolve_expr_sort_datatype() {
    let hint = ParamSortHint::Datatype("ResultIntInt".to_string());
    let sort = ParamSortHint::resolve_expr_sort(Some(hint));
    match sort {
        ExprSort::Datatype(id) => {
            assert_eq!(
                crate::formula::resolve_sort_name(id),
                "ResultIntInt",
                "Datatype hint must resolve to ExprSort::Datatype with correct interned name"
            );
        }
        other => panic!("expected ExprSort::Datatype, got {other:?}"),
    }
}

#[test]
fn test_type_invariant_method_name_sanitizes_suffix() {
    // _ → __, :: → _P__P_, < → _LT_, > → _GT_ (#687)
    assert_eq!(
        type_invariant_method_name("my_crate::SmallNum<T>"),
        "__trust_wp_invariant_my__crate_P__P_SmallNum_LT_T_GT_"
    );
}

#[test]
fn test_type_invariant_method_name_no_collision() {
    // #687: Foo<T> and Foo_T_ must produce distinct names.
    // _ is escaped to __ so encoding tokens can't collide with literals.
    let name_generic = type_invariant_method_name("Foo<T>");
    let name_underscored = type_invariant_method_name("Foo_T_");
    assert_ne!(name_generic, name_underscored);
    assert_eq!(name_generic, "__trust_wp_invariant_Foo_LT_T_GT_");
    assert_eq!(name_underscored, "__trust_wp_invariant_Foo__T__");
}

#[test]
fn test_type_invariant_method_name_complex_generic() {
    let name = type_invariant_method_name("HashMap<K, V>");
    assert_eq!(name, "__trust_wp_invariant_HashMap_LT_K_C__S_V_GT_");
}

#[test]
fn test_type_invariant_method_name_injective_underscore_encoding() {
    // Verify encoding is injective: "A_LT_B" (literal) must differ from "A<B"
    let literal = type_invariant_method_name("A_LT_B");
    let encoded = type_invariant_method_name("A<B");
    assert_ne!(literal, encoded);
    // "A_LT_B" → "A__LT__B" (underscores escaped)
    assert_eq!(literal, "__trust_wp_invariant_A__LT__B");
    // "A<B" → "A_LT_B" (< encoded)
    assert_eq!(encoded, "__trust_wp_invariant_A_LT_B");
}

#[test]
fn test_is_invariant_method_name() {
    assert!(is_invariant_method_name("invariant"));
    assert!(is_invariant_method_name("invariants"));
    assert!(is_invariant_method_name("__trust_wp_invariant_NonZero"));
    assert!(!is_invariant_method_name("len"));
    assert!(!is_invariant_method_name("invariant_check"));
}

#[test]
fn redetect_recursion_ignores_builtin_method_call_name_coincidence() {
    use std::sync::Arc;

    // Memory::index_logic body `self.0[i]` parses to an `index_logic`
    // MethodCall on the Vec field — NOT a self-call.
    let body = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Var("i".to_string(), None)],
    };
    let mut lf = LogicFnDef::new(
        "index_logic".to_string(),
        "creusot_test::Memory::index_logic".to_string(),
        vec!["self".to_string(), "i".to_string()],
        body,
    )
    .detect_recursion();
    // Pre-routing name-based detection over-approximates: flags recursive.
    assert!(lf.is_recursive());
    // Post-routing (LogicFnCall-only) detection clears the false flag.
    lf.redetect_recursion_logic_calls_only();
    assert!(!lf.is_recursive());
}

#[test]
fn redetect_recursion_keeps_genuine_logic_fn_self_call() {
    use std::sync::Arc;

    use crate::formula::BinOp;

    // A genuinely recursive shadowed impl: self-dispatch was routed to
    // LogicFnCall by the shadowed-builtin rewrite.
    let body = PureExpr::LogicFnCall {
        name: "index_logic".to_string(),
        args: vec![
            PureExpr::Var("self".to_string(), None),
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), None)),
                BinOp::Sub,
                Arc::new(PureExpr::Int(1)),
            ),
        ],
    };
    let mut lf = LogicFnDef::new(
        "index_logic".to_string(),
        "creusot_test::Memory::index_logic".to_string(),
        vec!["self".to_string(), "i".to_string()],
        body,
    );
    lf.redetect_recursion_logic_calls_only();
    assert!(lf.is_recursive());
}
