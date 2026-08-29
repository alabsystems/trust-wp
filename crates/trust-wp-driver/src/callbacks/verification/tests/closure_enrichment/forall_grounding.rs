// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use crate::callbacks::closure_enrichment::{
    strip_receiver_state_wrappers, try_ground_forall_obligation, ClosureSpec,
};

fn closure_spec(
    receiver_name: &str,
    capture_bindings: Vec<(usize, String)>,
    requires_exprs: Vec<PureExpr>,
    ensures_exprs: Vec<PureExpr>,
) -> ClosureSpec {
    ClosureSpec {
        receiver_name: receiver_name.to_string(),
        param_names: vec![],
        capture_bindings,
        requires_exprs,
        ensures_exprs,
    }
}

#[test]
fn strip_receiver_state_wrappers_removes_nested_final_and_deref() {
    let base = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple1".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let wrapped = PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(base.clone()))));

    let stripped = strip_receiver_state_wrappers(&wrapped);
    assert_eq!(stripped, base);
}

/// The `__forall_post_state` variable used in `try_ground_forall_obligation`
/// should have `None` sort (untyped), not `ExprSort::Int`, because it
/// represents a closure capture environment (a product type). (#1187)
#[test]
fn try_ground_forall_post_state_has_none_sort() {
    // Closure captures two fields: (0, "a") and (1, "b")
    let capture_bindings: Vec<(usize, String)> = vec![(0, "a".to_string()), (1, "b".to_string())];
    // Ensures: a == old(a) + 1 (i.e., capture "a" incremented)
    let ensures_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("a".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                "a".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    // Requires: a >= 0
    let requires_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("a".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );

    let closure_specs: Vec<ClosureSpec> = vec![closure_spec(
        "closure_env",
        capture_bindings,
        vec![requires_expr],
        vec![ensures_expr],
    )];

    // Build: Forall st, r: postcondition_mut(RECV, args, st, r) ==> req(st)
    let recv = PureExpr::Var("closure_env".to_string(), None);
    let args = PureExpr::Var("call_args".to_string(), None);
    let st = PureExpr::Var("st".to_string(), None);
    let r = PureExpr::Var("r".to_string(), None);

    let postcond_call = PureExpr::MethodCall {
        receiver: Arc::new(recv),
        method: "postcondition_mut".to_string(),
        args: vec![args, st, r],
    };
    let consequent = PureExpr::Bool(true);
    let implication = PureExpr::BinOp(
        Arc::new(postcond_call),
        BinOp::Implies,
        Arc::new(consequent),
    );
    let forall = PureExpr::Forall {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(implication),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    let result = try_ground_forall_obligation(&forall, &closure_specs).expect("should ground");

    // Walk the result tree and find __forall_post_state variables.
    // They should all have None sort, not Some(ExprSort::Int).
    fn find_post_state_sorts(expr: &PureExpr, found: &mut Vec<Option<ExprSort>>) {
        match expr {
            PureExpr::Var(name, sort) if name == "__forall_post_state" => {
                found.push(sort.clone());
            }
            PureExpr::BinOp(l, _, r) => {
                find_post_state_sorts(l, found);
                find_post_state_sorts(r, found);
            }
            PureExpr::LogicFnCall { args, .. } => {
                for arg in args {
                    find_post_state_sorts(arg, found);
                }
            }
            PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner)
            | PureExpr::UnOp(_, inner) => find_post_state_sorts(inner, found),
            PureExpr::MethodCall { receiver, args, .. } => {
                find_post_state_sorts(receiver, found);
                for arg in args {
                    find_post_state_sorts(arg, found);
                }
            }
            _ => {}
        }
    }

    let mut sorts = Vec::new();
    find_post_state_sorts(&result, &mut sorts);
    assert!(
        !sorts.is_empty(),
        "expected __forall_post_state in grounded result, got: {result:?}"
    );
    for sort in &sorts {
        assert_eq!(
            sort, &None,
            "__forall_post_state should have None sort (untyped), not {:?}; \
             closure captures are product types, not Int",
            sort
        );
    }
}

/// `try_ground_forall_obligation` produces `ensures ==> requires` with capture
/// projections applied to the fresh post-state variable.
#[test]
fn try_ground_forall_obligation_projects_captures_to_tuple_fields() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    // Single capture: (0, "x")
    let capture_bindings: Vec<(usize, String)> = vec![(0, "x".to_string())];
    // Ensures: x == old(x) + 1
    let ensures_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    // Requires: x >= 0
    let requires_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );

    let closure_specs: Vec<ClosureSpec> = vec![closure_spec(
        "env",
        capture_bindings,
        vec![requires_expr],
        vec![ensures_expr],
    )];

    let recv = PureExpr::Var("env".to_string(), None);
    let postcond = PureExpr::MethodCall {
        receiver: Arc::new(recv),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("args".to_string(), None),
            PureExpr::Var("st".to_string(), None),
            PureExpr::Var("r".to_string(), None),
        ],
    };
    let forall = PureExpr::Forall {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(postcond),
                BinOp::Implies,
                Arc::new(PureExpr::Bool(true)),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    let result = try_ground_forall_obligation(&forall, &closure_specs).expect("should ground");

    // The result should contain tuple_field_logic_fn_name(0) calls for the
    // capture projection on __forall_post_state.
    let expected_fn = tuple_field_logic_fn_name(0);
    fn contains_logic_fn(expr: &PureExpr, name: &str) -> bool {
        match expr {
            PureExpr::LogicFnCall {
                name: fn_name,
                args,
            } => fn_name == name || args.iter().any(|a| contains_logic_fn(a, name)),
            PureExpr::BinOp(l, _, r) => contains_logic_fn(l, name) || contains_logic_fn(r, name),
            PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner)
            | PureExpr::UnOp(_, inner) => contains_logic_fn(inner, name),
            PureExpr::MethodCall { receiver, args, .. } => {
                contains_logic_fn(receiver, name) || args.iter().any(|a| contains_logic_fn(a, name))
            }
            _ => false,
        }
    }

    assert!(
        contains_logic_fn(&result, &expected_fn),
        "expected {expected_fn} in grounded result for capture projection, got: {result:?}"
    );
}

#[test]
fn try_ground_forall_obligation_non_implies_returns_none() {
    let closure_specs: Vec<ClosureSpec> = vec![closure_spec(
        "env",
        vec![(0, "x".to_string())],
        vec![PureExpr::Bool(true)],
        vec![PureExpr::Bool(true)],
    )];

    // A forall that wraps a plain expression (not Implies) — should return None
    let forall = PureExpr::Forall {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Bool(true)),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    assert!(
        try_ground_forall_obligation(&forall, &closure_specs).is_none(),
        "non-implies body should not ground"
    );
}

#[test]
fn try_ground_forall_obligation_empty_specs_returns_none() {
    let closure_specs: Vec<ClosureSpec> = vec![];

    let recv = PureExpr::Var("env".to_string(), None);
    let postcond = PureExpr::MethodCall {
        receiver: Arc::new(recv),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("a".to_string(), None),
            PureExpr::Var("st".to_string(), None),
            PureExpr::Var("r".to_string(), None),
        ],
    };
    let forall = PureExpr::Forall {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(postcond),
                BinOp::Implies,
                Arc::new(PureExpr::Bool(true)),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    assert!(
        try_ground_forall_obligation(&forall, &closure_specs).is_none(),
        "empty closure specs means no grounding is possible"
    );
}

#[test]
fn try_ground_forall_obligation_non_postcondition_mut_returns_none() {
    let closure_specs: Vec<ClosureSpec> = vec![closure_spec(
        "env",
        vec![(0, "x".to_string())],
        vec![PureExpr::Bool(true)],
        vec![PureExpr::Bool(true)],
    )];

    // Antecedent uses "some_other_method" instead of "postcondition_mut"
    let recv = PureExpr::Var("env".to_string(), None);
    let call = PureExpr::MethodCall {
        receiver: Arc::new(recv),
        method: "some_other_method".to_string(),
        args: vec![
            PureExpr::Var("a".to_string(), None),
            PureExpr::Var("st".to_string(), None),
            PureExpr::Var("r".to_string(), None),
        ],
    };
    let forall = PureExpr::Forall {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(call),
                BinOp::Implies,
                Arc::new(PureExpr::Bool(true)),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    assert!(
        try_ground_forall_obligation(&forall, &closure_specs).is_none(),
        "non-postcondition_mut method should not match"
    );
}

#[test]
fn try_ground_forall_obligation_uses_matching_receiver_instead_of_first_spec() {
    let closure_specs = vec![
        closure_spec(
            "c1",
            vec![],
            vec![PureExpr::BinOp(
                Arc::new(PureExpr::Int(11)),
                BinOp::Eq,
                Arc::new(PureExpr::Int(11)),
            )],
            vec![PureExpr::BinOp(
                Arc::new(PureExpr::Int(1)),
                BinOp::Eq,
                Arc::new(PureExpr::Int(1)),
            )],
        ),
        closure_spec(
            "c2",
            vec![],
            vec![PureExpr::BinOp(
                Arc::new(PureExpr::Int(22)),
                BinOp::Eq,
                Arc::new(PureExpr::Int(22)),
            )],
            vec![PureExpr::BinOp(
                Arc::new(PureExpr::Int(2)),
                BinOp::Eq,
                Arc::new(PureExpr::Int(2)),
            )],
        ),
    ];
    let postcond = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c2".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("args".to_string(), None),
            PureExpr::Var("st".to_string(), None),
            PureExpr::Var("r".to_string(), None),
        ],
    };
    let forall = PureExpr::Forall {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(postcond),
                BinOp::Implies,
                Arc::new(PureExpr::Bool(true)),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    let grounded = try_ground_forall_obligation(&forall, &closure_specs).expect("should ground");
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(2)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(2)),
        )),
        BinOp::Implies,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(22)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(22)),
        )),
    );
    assert_eq!(grounded, expected);
}

#[test]
fn try_ground_forall_obligation_ambiguous_receiver_returns_none() {
    let closure_specs = vec![
        closure_spec(
            "c",
            vec![],
            vec![PureExpr::Bool(true)],
            vec![PureExpr::Bool(true)],
        ),
        closure_spec(
            "c",
            vec![],
            vec![PureExpr::Bool(false)],
            vec![PureExpr::Bool(false)],
        ),
    ];
    let postcond = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("args".to_string(), None),
            PureExpr::Var("st".to_string(), None),
            PureExpr::Var("r".to_string(), None),
        ],
    };
    let forall = PureExpr::Forall {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(postcond),
                BinOp::Implies,
                Arc::new(PureExpr::Bool(true)),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    assert!(try_ground_forall_obligation(&forall, &closure_specs).is_none());
}

#[test]
fn try_ground_forall_obligation_matches_wrapped_receiver_name() {
    let closure_specs = vec![closure_spec(
        "c2",
        vec![],
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Int(22)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(22)),
        )],
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Int(2)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(2)),
        )],
    )];
    let wrapped_receiver = PureExpr::View(Arc::new(PureExpr::Old(Arc::new(PureExpr::Final(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "c2".to_string(),
            None,
        )))),
    )))));
    let postcond = PureExpr::MethodCall {
        receiver: Arc::new(wrapped_receiver),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("args".to_string(), None),
            PureExpr::Var("st".to_string(), None),
            PureExpr::Var("r".to_string(), None),
        ],
    };
    let forall = PureExpr::Forall {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Forall {
            var: "r".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(postcond),
                BinOp::Implies,
                Arc::new(PureExpr::Bool(true)),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };

    let grounded = try_ground_forall_obligation(&forall, &closure_specs).expect("should ground");
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(2)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(2)),
        )),
        BinOp::Implies,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(22)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(22)),
        )),
    );
    assert_eq!(grounded, expected);
}
