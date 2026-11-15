// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for type-directed post-processing of logic function definitions.

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::{
    formula::{intern_sort_name, ExprSort, PureExpr},
    logic::LogicMode,
};

use super::*;

fn make_logic_fn(name: &str, full_path: &str, body: &str) -> LogicFunction {
    LogicFunction {
        name: name.to_string(),
        full_path: full_path.to_string(),
        params: vec!["self".to_string()],
        requires: Vec::new(),
        written_requires: 0,
        ensures: Vec::new(),
        variants: Vec::new(),
        is_opaque: false,
        is_trusted: false,
        is_law: false,
        mode: LogicMode::Default,
        is_trait_method: false,
        is_associated_fn: false,
        param_sort_hints: vec![None],
        param_int_widths: Vec::new(),
        return_sort_hint: None,
        body_text: Some(body.to_string()),
        deep_model_dispatch_targets: None,
        param_bindings: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// Type invariant tests
// ---------------------------------------------------------------------------

#[test]
fn test_is_invariant_impl_creusot_style() {
    let lf = make_logic_fn(
        "invariant",
        "<Sum10 as creusot_std::Invariant>::invariant",
        "self.a + self.b == 10",
    );
    assert!(is_invariant_impl(&lf));
}

#[test]
fn test_is_invariant_impl_trust_wp_style() {
    let lf = make_logic_fn(
        "invariant",
        "<NonZero as trust_wp_std::Invariant>::invariant",
        "self > 0",
    );
    assert!(is_invariant_impl(&lf));
}

#[test]
fn test_is_invariant_impl_rejects_non_invariant() {
    let lf = make_logic_fn("max", "crate::specs::max", "if a > b { a } else { b }");
    assert!(!is_invariant_impl(&lf));
}

#[test]
fn test_is_invariant_impl_rejects_invariant_name_wrong_path() {
    // A function named "invariant" but not in an Invariant impl
    let lf = make_logic_fn("invariant", "crate::my_mod::invariant", "true");
    assert!(!is_invariant_impl(&lf));
}

#[test]
fn test_to_type_invariant_def_basic() {
    let lf = make_logic_fn("invariant", "<NonZero as Invariant>::invariant", "self > 0");
    let def = to_type_invariant_def(&lf).expect("should parse");
    assert_eq!(def.type_name(), "NonZero");
    assert_eq!(def.self_param(), "self");
    assert_eq!(def.param_sort(), None);
    // Body should be a BinOp Gt
    assert!(matches!(
        def.body(),
        PureExpr::BinOp(_, trust_wp_core::formula::BinOp::Gt, _)
    ));
}

#[test]
fn test_to_type_invariant_def_with_bool_sort() {
    let mut lf = make_logic_fn("invariant", "<Wrapper as Invariant>::invariant", "true");
    lf.param_sort_hints = vec![Some(ExprSort::Bool)];
    let def = to_type_invariant_def(&lf).expect("should parse");
    assert_eq!(def.type_name(), "Wrapper");
    assert_eq!(def.param_sort(), Some(&ExprSort::Bool));
}

#[test]
fn test_to_type_invariant_def_collapses_newtype_projection_for_datatype_sort() {
    // Single-field struct invariants are always simplified to scalar form
    // because MIR-level aggregate collapse (`Self(n)` → `n`) produces
    // scalar return expressions. The invariant body must match. (#2669)
    let mut lf = make_logic_fn(
        "invariant",
        "<PositiveU32 as Invariant>::invariant",
        "self.0@ > 0",
    );
    let datatype_sort = ExprSort::Datatype(intern_sort_name("crate::PositiveU32"));
    lf.param_sort_hints = vec![Some(datatype_sort.clone())];

    let def = to_type_invariant_def(&lf).expect("should parse");

    assert_eq!(def.param_sort(), Some(&datatype_sort));
    assert!(
        def.is_newtype(),
        "single-field struct invariants must be newtype-simplified to match MIR aggregate collapse",
    );
    // Body should be collapsed: `self > 0` (not `View(tuple_get_0(self)) > 0`)
    assert!(
        matches!(
            def.body(),
            PureExpr::BinOp(lhs, trust_wp_core::formula::BinOp::Gt, rhs)
                if matches!(lhs.as_ref(), PureExpr::Var(var, _) if var == "self")
                   && matches!(rhs.as_ref(), PureExpr::Int(0))
        ),
        "single-field struct invariant body should collapse to `self > 0`: {:?}",
        def.body()
    );
}

#[test]
fn test_to_type_invariant_def_preserves_qualified_type_path() {
    let lf = make_logic_fn(
        "invariant",
        "<my_crate::a::Counter as Invariant>::invariant",
        "self > 0",
    );
    let def = to_type_invariant_def(&lf).expect("should parse");
    assert_eq!(def.type_name(), "my_crate::a::Counter");
}

#[test]
fn test_to_type_invariant_def_no_body() {
    let mut lf = make_logic_fn("invariant", "<Foo as Invariant>::invariant", "");
    lf.body_text = None;
    assert!(to_type_invariant_def(&lf).is_none());
}

// ---------------------------------------------------------------------------
// extract_invariant_type_name tests
// ---------------------------------------------------------------------------

#[test]
fn test_extract_invariant_type_name_simple() {
    assert_eq!(
        extract_invariant_type_name("<Counter as Invariant>::invariant"),
        "Counter"
    );
}

#[test]
fn test_extract_invariant_type_name_with_module_path() {
    assert_eq!(
        extract_invariant_type_name("<my_crate::Counter as creusot_std::Invariant>::invariant"),
        "my_crate::Counter"
    );
}

#[test]
fn test_extract_invariant_type_name_strips_generics() {
    // #686: Generic params must be stripped to match def_path_str output
    assert_eq!(
        extract_invariant_type_name("<Bounded<i32> as Invariant>::invariant"),
        "Bounded"
    );
}

#[test]
fn test_extract_invariant_type_name_strips_nested_generics() {
    assert_eq!(
        extract_invariant_type_name("<my_crate::Pair<A, B> as Invariant>::invariant"),
        "my_crate::Pair"
    );
}

#[test]
fn test_extract_invariant_type_name_crate_prefixed() {
    // #1370: When rustc formats the path with a crate prefix before `<`,
    // the type name must include the crate qualifier to match def_path_str output.
    assert_eq!(
        extract_invariant_type_name("creusot_test::<SumTo10 as creusot_std::Invariant>::invariant"),
        "creusot_test::SumTo10"
    );
}

#[test]
fn test_extract_invariant_type_name_crate_prefixed_qualified_inner() {
    // When the type inside `<>` already has a module qualifier (contains `::`),
    // the prefix is NOT prepended — the inner path is treated as fully qualified.
    assert_eq!(
        extract_invariant_type_name(
            "my_crate::<sub::Counter as creusot_std::Invariant>::invariant"
        ),
        "sub::Counter"
    );
}

#[test]
fn test_extract_invariant_type_name_fallback() {
    // When the path doesn't match the expected pattern, returns the full path
    assert_eq!(
        extract_invariant_type_name("some_random_path"),
        "some_random_path"
    );
}

// ---------------------------------------------------------------------------
// Newtype simplification tests
// ---------------------------------------------------------------------------

#[test]
fn test_has_higher_tuple_field_access_in_let_assume() {
    // tuple_get_1(self) nested inside a LetAssume body should be detected (#917)
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_1".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }),
    };
    assert!(has_higher_tuple_field_access(&expr));
}

#[test]
fn test_has_higher_tuple_field_access_in_let_assume_assumption() {
    // tuple_get_1(self) nested inside a LetAssume assumption should be detected (#917)
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_1".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }),
        body: Arc::new(PureExpr::Bool(true)),
    };
    assert!(has_higher_tuple_field_access(&expr));
}

#[test]
fn test_has_higher_tuple_field_access_in_let_obligation() {
    // tuple_get_2(self) nested inside a LetObligation obligation should be detected (#917)
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_2".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }),
        body: Arc::new(PureExpr::Bool(true)),
    };
    assert!(has_higher_tuple_field_access(&expr));
}

#[test]
fn test_has_higher_tuple_field_access_let_assume_no_false_positive() {
    // LetAssume with tuple_get_0 (not higher) should return false
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }),
    };
    assert!(!has_higher_tuple_field_access(&expr));
}

#[test]
fn test_simplify_newtype_view_in_expr_for_multiple_params() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }))),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(PureExpr::View(Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("rhs".to_string(), None)],
        }))),
    );
    let mut params = HashSet::new();
    params.insert("self".to_string());
    params.insert("rhs".to_string());

    let simplified = simplify_newtype_view_in_expr_for_params(expr, &params);
    assert_eq!(
        simplified,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Var("rhs".to_string(), None)),
        ),
    );
}

#[test]
fn test_simplify_newtype_view_recurses_into_old() {
    // old(@self.0) should simplify to old(self)
    let view_tuple_self = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("self".to_string(), None)],
    }));
    let expr = PureExpr::Old(Arc::new(view_tuple_self));
    let result = simplify_newtype_view_in_body(expr, "self");
    assert_eq!(
        result,
        PureExpr::Old(Arc::new(PureExpr::Var("self".to_string(), None))),
        "Old(View(tuple_get_0(self))) should simplify to Old(Var(self))"
    );
}

#[test]
fn test_simplify_newtype_view_recurses_into_match() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let view_tuple_self = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("self".to_string(), None)],
    }));
    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: view_tuple_self,
        }],
    };
    let result = simplify_newtype_view_in_body(expr, "self");
    assert_eq!(
        result,
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Var("self".to_string(), None),
            }],
        },
        "Match arm body should have View(tuple_get_0(self)) simplified"
    );
}

#[test]
fn test_simplify_newtype_view_recurses_into_deref_and_final() {
    let view_tuple_self = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("self".to_string(), None)],
    }));

    // Deref(*(@self.0)) should simplify to Deref(self)
    let deref_expr = PureExpr::Deref(Arc::new(view_tuple_self.clone()));
    let result = simplify_newtype_view_in_body(deref_expr, "self");
    assert_eq!(
        result,
        PureExpr::Deref(Arc::new(PureExpr::Var("self".to_string(), None))),
    );

    // Final(^(@self.0)) should simplify to Final(self)
    let final_expr = PureExpr::Final(Arc::new(view_tuple_self));
    let result = simplify_newtype_view_in_body(final_expr, "self");
    assert_eq!(
        result,
        PureExpr::Final(Arc::new(PureExpr::Var("self".to_string(), None))),
    );
}

#[test]
fn test_simplify_newtype_view_preserves_method_receiver() {
    let receiver = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("self".to_string(), None)],
    }));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver.clone()),
        method: "len".to_string(),
        args: vec![],
    };

    let result = simplify_newtype_view_in_body(expr, "self");
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "len".to_string(),
            args: vec![],
        },
        "method receivers must preserve self.0@ so collection dispatch sees the inner field sort"
    );
}

#[test]
fn test_simplify_newtype_view_preserves_nested_method_receiver() {
    let field_view = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("self".to_string(), None)],
    }));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(field_view.clone()),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Var("i".to_string(), None)],
        }),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };

    let result = simplify_newtype_view_in_body(expr, "self");
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(field_view),
                method: "index_logic".to_string(),
                args: vec![PureExpr::Var("i".to_string(), None)],
            }),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        },
        "nested receivers like self.0@[i] must keep the field projection intact"
    );
}

#[test]
fn test_simplify_newtype_view_rewrites_quantifier_triggers() {
    let field_view = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("self".to_string(), None)],
    }));
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(field_view.clone()),
            trust_wp_core::formula::BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )),
        triggers: vec![vec![field_view]],
    };

    let result = simplify_newtype_view_in_body(expr, "self");
    assert_eq!(
        result,
        PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("self".to_string(), None)),
                trust_wp_core::formula::BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
            triggers: vec![vec![PureExpr::Var("self".to_string(), None)]],
        },
        "quantifier triggers should simplify self.0@ consistently with the body"
    );
}

#[test]
fn test_simplify_newtype_view_in_expr_keeps_non_newtype_params() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }))),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(PureExpr::View(Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("rhs".to_string(), None)],
        }))),
    );
    let mut params = HashSet::new();
    params.insert("self".to_string());

    let simplified = simplify_newtype_view_in_expr_for_params(expr, &params);
    assert_eq!(
        simplified,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::View(Arc::new(PureExpr::LogicFnCall {
                name: "__trust_wp_tuple_get_0".to_string(),
                args: vec![PureExpr::Var("rhs".to_string(), None)],
            }))),
        ),
    );
}
