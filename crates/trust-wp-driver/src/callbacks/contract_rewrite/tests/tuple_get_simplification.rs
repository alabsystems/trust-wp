// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn simplify_newtype_tuple_get_0_basic() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    // tuple_get_0(self) -> self
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("self".to_string(), None)],
    };
    let result = simplify_newtype_field_access_expr(&expr, &params);
    assert_eq!(result, PureExpr::Var("self".to_string(), None));
}

#[test]
fn simplify_newtype_tuple_get_0_of_mut_ref_param_projects_deref() {
    let mut params = HashSet::new();
    params.insert("x".to_string());

    let nonzero_sort = ExprSort::Datatype(intern_sort_name("NonZero"));
    let x = PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::MutRef(Box::new(nonzero_sort))),
    );

    let expr = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![x.clone()],
    }));

    let result = simplify_newtype_field_access_expr(&expr, &params);

    assert_eq!(
        result,
        PureExpr::View(Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Deref(Arc::new(x))],
        })),
    );
}

#[test]
fn simplify_newtype_tuple_get_0_of_projected_mut_ref_param_is_preserved() {
    let mut params = HashSet::new();
    params.insert("x".to_string());

    let nonzero_sort = ExprSort::Datatype(intern_sort_name("NonZero"));
    let x = PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::MutRef(Box::new(nonzero_sort))),
    );
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Deref(Arc::new(x.clone()))],
    };

    let result = simplify_newtype_field_access_expr(&expr, &params);

    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Deref(Arc::new(x))],
        },
    );
}

#[test]
fn simplify_newtype_tuple_get_0_of_datatype_param_still_collapses() {
    let mut params = HashSet::new();
    params.insert("x".to_string());

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("NonZero"))),
        )],
    };

    let result = simplify_newtype_field_access_expr(&expr, &params);

    assert_eq!(
        result,
        PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("NonZero"))),
        ),
    );
}

/// Regression: tuple_get_0(x) should NOT simplify when x is not a newtype param.
#[test]
fn simplify_newtype_tuple_get_0_non_newtype_param_preserved() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    // tuple_get_0(rhs) should NOT simplify -- rhs is not in newtype_params
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("rhs".to_string(), None)],
    };
    let result = simplify_newtype_field_access_expr(&expr, &params);
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("rhs".to_string(), None)],
        },
        "tuple_get_0 on non-newtype param should be preserved"
    );
}

/// Regression: tuple_get_1(self) should NOT simplify even for newtype params.
/// Only field-0 is identity for newtypes.
#[test]
fn simplify_newtype_tuple_get_1_not_simplified() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![PureExpr::Var("self".to_string(), None)],
    };
    let result = simplify_newtype_field_access_expr(&expr, &params);
    // Should be unchanged -- tuple_get_1 is not identity for any type
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_1".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        },
    );
}

/// Regression: "self.0" Var pattern should simplify to "self" for newtype params.
#[test]
fn simplify_newtype_var_dot_0_closure_artifact() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    let expr = PureExpr::Var("self.0".to_string(), None);
    let result = simplify_newtype_field_access_expr(&expr, &params);
    assert_eq!(result, PureExpr::Var("self".to_string(), None));
}

/// Regression: "rhs.0" should NOT simplify when rhs is not a newtype param.
#[test]
fn simplify_newtype_var_dot_0_non_newtype_preserved() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    let expr = PureExpr::Var("rhs.0".to_string(), None);
    let result = simplify_newtype_field_access_expr(&expr, &params);
    assert_eq!(
        result,
        PureExpr::Var("rhs.0".to_string(), None),
        "rhs.0 should be preserved when rhs is not a newtype param"
    );
}

/// Algorithm audit: simplification should recurse into nested expressions.
/// Verify BinOp(tuple_get_0(self), Ge, Int(0)) -> BinOp(self, Ge, Int(0)).
#[test]
fn simplify_newtype_recurses_into_binop() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let result = simplify_newtype_field_access_expr(&expr, &params);
    assert_eq!(
        result,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
    );
}

/// Algorithm audit: tuple_get_0(old(self)) should simplify to old(self)
/// since old() wraps a newtype param.
#[test]
fn simplify_newtype_tuple_get_0_of_old() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Old(Arc::new(PureExpr::Var(
            "self".to_string(),
            None,
        )))],
    };
    let result = simplify_newtype_field_access_expr(&expr, &params);
    assert_eq!(
        result,
        PureExpr::Old(Arc::new(PureExpr::Var("self".to_string(), None))),
    );
}

/// Algorithm audit: empty newtype_params should leave all expressions unchanged.
#[test]
fn simplify_newtype_empty_params_is_identity() {
    let params = HashSet::new();

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("self".to_string(), None)],
    };
    let result = simplify_newtype_field_access_expr(&expr, &params);
    // With empty params, nothing should be simplified
    assert_eq!(result, expr);
}

/// Algorithm audit: is_newtype_param_expr correctly identifies newtype params
/// through Deref/Old/Final wrappers.
#[test]
fn is_newtype_param_expr_through_wrappers() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    assert!(is_newtype_param_expr(
        &PureExpr::Var("self".to_string(), None),
        &params
    ));
    assert!(is_newtype_param_expr(
        &PureExpr::Deref(Arc::new(PureExpr::Var("self".to_string(), None))),
        &params
    ));
    assert!(is_newtype_param_expr(
        &PureExpr::Old(Arc::new(PureExpr::Var("self".to_string(), None))),
        &params
    ));
    assert!(is_newtype_param_expr(
        &PureExpr::Final(Arc::new(PureExpr::Var("self".to_string(), None))),
        &params
    ));
    // Non-param should return false
    assert!(!is_newtype_param_expr(
        &PureExpr::Var("rhs".to_string(), None),
        &params
    ));
    // Non-Var/Deref/Old/Final should return false
    assert!(!is_newtype_param_expr(&PureExpr::Int(42), &params));
}

#[test]
fn annotate_var_sorts_promotes_turbofish_placeholder_const_generic() {
    let expr = PureExpr::LogicFnCall {
        name: "add_one_logic".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: TURBOFISH_ARG_WRAPPER_NAME.to_string(),
            args: vec![PureExpr::Var(
                "M".to_string(),
                Some(ExprSort::TypeParam(intern_sort_name("M"))),
            )],
        }],
    };
    let sort_map = HashMap::from([("M".to_string(), ExprSort::Int)]);

    let annotated = annotate_var_sorts(&expr, &sort_map);
    let normalized = normalize_turbofish_logic_fn_expr(&annotated);

    assert_eq!(
        normalized,
        PureExpr::LogicFnCall {
            name: "add_one_logic".to_string(),
            args: vec![PureExpr::Var("M".to_string(), Some(ExprSort::Int))],
        }
    );
}

#[test]
fn normalize_turbofish_logic_fn_expr_drops_type_only_prefix_args() {
    let expr = PureExpr::LogicFnCall {
        name: "size_of_logic".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: TURBOFISH_ARG_WRAPPER_NAME.to_string(),
            args: vec![PureExpr::Var(
                "bool".to_string(),
                Some(ExprSort::TypeParam(intern_sort_name("bool"))),
            )],
        }],
    };

    // For layout intrinsics, the type name is encoded into the function name
    // so the encoder can assert concrete layout axioms. (#2324)
    assert_eq!(
        normalize_turbofish_logic_fn_expr(&expr),
        PureExpr::LogicFnCall {
            name: "size_of_logic__bool".to_string(),
            args: vec![],
        }
    );
}

/// Algorithm audit: simplification inside Forall quantifier body works correctly.
#[test]
fn simplify_newtype_inside_forall_body() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    // forall<i> { tuple_get_0(self) >= i }
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: "__trust_wp_tuple_get_0".to_string(),
                args: vec![PureExpr::Var("self".to_string(), None)],
            }),
            BinOp::Ge,
            Arc::new(PureExpr::Var("i".to_string(), None)),
        )),
        triggers: vec![],
    };
    let result = simplify_newtype_field_access_expr(&expr, &params);
    // Should simplify tuple_get_0(self) -> self inside the body
    assert_eq!(
        result,
        PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("self".to_string(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Var("i".to_string(), None)),
            )),
            triggers: vec![],
        },
    );
}

/// Algorithm audit: simplification inside Let binding body and value works.
#[test]
fn simplify_newtype_inside_let_binding() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    // let x = tuple_get_0(self) in x > 0
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
    };
    let result = simplify_newtype_field_access_expr(&expr, &params);
    assert_eq!(
        result,
        PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::Var("self".to_string(), None)),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )),
        },
    );
}

/// Algorithm audit: multi-arg tuple_get_0 should NOT be simplified.
/// The simplification only applies to unary calls.
#[test]
fn simplify_newtype_multi_arg_tuple_get_not_simplified() {
    let mut params = HashSet::new();
    params.insert("self".to_string());

    // Malformed: tuple_get_0(self, rhs) -- should not be simplified
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![
            PureExpr::Var("self".to_string(), None),
            PureExpr::Var("rhs".to_string(), None),
        ],
    };
    let result = simplify_newtype_field_access_expr(&expr, &params);
    // Should recurse into args but not simplify the call itself
    assert_eq!(result, expr);
}
