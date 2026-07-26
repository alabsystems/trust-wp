// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(clippy::approx_constant)]

//! Tests for `PureExpr::any_recursive`, `PureExpr::for_each_recursive`,
//! and `PureExpr::rewrite_bottom_up` — three recursive traversal methods
//! on the core expression AST that previously had zero unit coverage.

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, ExprSort, FloatBits, MatchArm, Pattern, PureExpr, UnOp};

// ── helpers ──

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn int(n: i64) -> PureExpr {
    PureExpr::Int(n)
}

fn arc(e: PureExpr) -> Arc<PureExpr> {
    Arc::new(e)
}

fn add(left: PureExpr, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(arc(left), BinOp::Add, arc(right))
}

// ════════════════════════════════════════════════════════════════════
// any_recursive
// ════════════════════════════════════════════════════════════════════

#[test]
fn any_recursive_literal_true() {
    let e = int(42);
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Int(42))));
}

#[test]
fn any_recursive_literal_false() {
    let e = int(42);
    assert!(!e.any_recursive(|n| matches!(n, PureExpr::Int(99))));
}

#[test]
fn any_recursive_bool_literal() {
    let e = PureExpr::Bool(true);
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Bool(true))));
    assert!(!e.any_recursive(|n| matches!(n, PureExpr::Int(_))));
}

#[test]
fn any_recursive_float_literal() {
    let e = PureExpr::Float(FloatBits::from_f64(3.14));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Float(_))));
}

#[test]
fn any_recursive_var() {
    let e = var("x");
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "x")));
    assert!(!e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "y")));
}

#[test]
fn any_recursive_binop_finds_deep_child() {
    let e = add(add(int(1), var("x")), int(3));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "x")));
}

#[test]
fn any_recursive_unop() {
    let e = PureExpr::UnOp(UnOp::Neg, arc(var("x")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "x")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::UnOp(UnOp::Neg, _))));
}

#[test]
fn any_recursive_old() {
    let e = PureExpr::Old(arc(var("x")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "x")));
}

#[test]
fn any_recursive_deref() {
    let e = PureExpr::Deref(arc(var("p")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "p")));
}

#[test]
fn any_recursive_final() {
    let e = PureExpr::Final(arc(var("f")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "f")));
}

#[test]
fn any_recursive_view() {
    let e = PureExpr::View(arc(var("v")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "v")));
}

#[test]
fn any_recursive_ite() {
    let e = PureExpr::Ite(arc(PureExpr::Bool(true)), arc(int(1)), arc(var("z")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "z")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Bool(true))));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Int(1))));
}

#[test]
fn any_recursive_method_call_receiver_and_args() {
    let e = PureExpr::MethodCall {
        receiver: arc(var("seq")),
        method: "len".to_string(),
        args: vec![var("idx")],
    };
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "seq")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "idx")));
}

#[test]
fn any_recursive_forall_body_and_triggers() {
    let trigger_expr = var("trigger_x");
    let e = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: arc(add(var("x"), int(1))),
        triggers: vec![vec![trigger_expr]],
    };
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "trigger_x")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Int(1))));
}

#[test]
fn any_recursive_exists_body_and_triggers() {
    let e = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: arc(var("y")),
        triggers: vec![vec![var("z")]],
    };
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "y")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "z")));
}

#[test]
fn any_recursive_match_scrutinee_and_arms() {
    let e = PureExpr::Match {
        scrutinee: arc(var("s")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: var("arm_body"),
        }],
    };
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "s")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "arm_body")));
}

#[test]
fn any_recursive_logic_fn_call_args() {
    let e = PureExpr::LogicFnCall {
        name: "my_fn".to_string(),
        args: vec![var("a"), int(10)],
    };
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "a")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Int(10))));
}

#[test]
fn any_recursive_let_value_and_body() {
    let e = PureExpr::Let {
        var: "x".to_string(),
        value: arc(var("init")),
        body: arc(var("use")),
    };
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "init")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "use")));
}

#[test]
fn any_recursive_let_assume() {
    let e = PureExpr::LetAssume {
        assumption: arc(PureExpr::Bool(true)),
        body: arc(var("b")),
    };
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Bool(true))));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "b")));
}

#[test]
fn any_recursive_let_obligation() {
    let e = PureExpr::LetObligation {
        obligation: arc(var("pre")),
        body: arc(var("post")),
    };
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "pre")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "post")));
}

#[test]
fn any_recursive_closure_body() {
    let e = PureExpr::Closure {
        params: vec![("p".to_string(), None)],
        body: arc(add(var("p"), int(1))),
    };
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Var(name, _) if name == "p")));
    assert!(e.any_recursive(|n| matches!(n, PureExpr::Int(1))));
}

#[test]
fn any_recursive_short_circuits_on_root() {
    // If the root matches, children should not be checked.
    let mut call_count = 0;
    let e = add(int(1), int(2));
    e.any_recursive(|n| {
        call_count += 1;
        matches!(n, PureExpr::BinOp(..))
    });
    assert_eq!(call_count, 1, "should short-circuit on root match");
}

// ════════════════════════════════════════════════════════════════════
// for_each_recursive
// ════════════════════════════════════════════════════════════════════

#[test]
fn for_each_recursive_counts_all_nodes_binop() {
    // (1 + 2) has 3 nodes: BinOp, Int(1), Int(2)
    let e = add(int(1), int(2));
    let mut count = 0;
    e.for_each_recursive(|_| count += 1);
    assert_eq!(count, 3);
}

#[test]
fn for_each_recursive_visits_all_variant_types() {
    // Build expression with many variant types
    let inner = PureExpr::Closure {
        params: vec![("c".to_string(), None)],
        body: arc(PureExpr::LetObligation {
            obligation: arc(PureExpr::Bool(true)),
            body: arc(var("c")),
        }),
    };
    let e = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: arc(inner),
        triggers: vec![],
    };
    let mut variants = Vec::new();
    e.for_each_recursive(|n| {
        let tag = match n {
            PureExpr::Bool(_) => "Bool",
            PureExpr::Var(_, _) => "Var",
            PureExpr::Forall { .. } => "Forall",
            PureExpr::Closure { .. } => "Closure",
            PureExpr::LetObligation { .. } => "LetObligation",
            _ => "other",
        };
        variants.push(tag);
    });
    assert!(variants.contains(&"Forall"), "should visit Forall");
    assert!(variants.contains(&"Closure"), "should visit Closure");
    assert!(
        variants.contains(&"LetObligation"),
        "should visit LetObligation"
    );
    assert!(variants.contains(&"Bool"), "should visit Bool");
    assert!(variants.contains(&"Var"), "should visit Var");
}

#[test]
fn for_each_recursive_pre_order() {
    // For (1 + 2), pre-order is: BinOp, Int(1), Int(2)
    let e = add(int(1), int(2));
    let mut visit_order = Vec::new();
    e.for_each_recursive(|n| match n {
        PureExpr::BinOp(..) => visit_order.push("binop"),
        PureExpr::Int(v) => visit_order.push(if *v == 1 { "left" } else { "right" }),
        _ => {}
    });
    assert_eq!(visit_order, vec!["binop", "left", "right"]);
}

#[test]
fn for_each_recursive_unop_inner() {
    let e = PureExpr::UnOp(UnOp::Not, arc(PureExpr::Bool(true)));
    let mut count = 0;
    e.for_each_recursive(|_| count += 1);
    assert_eq!(count, 2, "UnOp + Bool = 2 nodes");
}

#[test]
fn for_each_recursive_old_deref_final_view() {
    // Chain: Old(Deref(Final(View(x))))
    let inner = PureExpr::View(arc(var("x")));
    let inner = PureExpr::Final(arc(inner));
    let inner = PureExpr::Deref(arc(inner));
    let e = PureExpr::Old(arc(inner));
    let mut count = 0;
    e.for_each_recursive(|_| count += 1);
    assert_eq!(count, 5, "Old + Deref + Final + View + Var = 5");
}

#[test]
fn for_each_recursive_ite_all_branches() {
    let e = PureExpr::Ite(arc(PureExpr::Bool(true)), arc(int(1)), arc(int(2)));
    let mut ints = Vec::new();
    e.for_each_recursive(|n| {
        if let PureExpr::Int(v) = n {
            ints.push(*v);
        }
    });
    assert_eq!(ints, vec![1, 2]);
}

#[test]
fn for_each_recursive_method_call() {
    let e = PureExpr::MethodCall {
        receiver: arc(var("r")),
        method: "m".to_string(),
        args: vec![var("a1"), var("a2")],
    };
    let mut vars = Vec::new();
    e.for_each_recursive(|n| {
        if let PureExpr::Var(name, _) = n {
            vars.push(name.clone());
        }
    });
    assert_eq!(vars, vec!["r", "a1", "a2"]);
}

#[test]
fn for_each_recursive_quantifier_triggers() {
    let e = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: arc(var("body_var")),
        triggers: vec![vec![var("t1")], vec![var("t2"), var("t3")]],
    };
    let mut vars = Vec::new();
    e.for_each_recursive(|n| {
        if let PureExpr::Var(name, _) = n {
            vars.push(name.clone());
        }
    });
    assert!(vars.contains(&"body_var".to_string()));
    assert!(vars.contains(&"t1".to_string()));
    assert!(vars.contains(&"t2".to_string()));
    assert!(vars.contains(&"t3".to_string()));
}

#[test]
fn for_each_recursive_match_arms() {
    let e = PureExpr::Match {
        scrutinee: arc(var("s")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Wildcard,
                body: int(1),
            },
            MatchArm {
                pattern: Pattern::Binding("b".to_string()),
                body: int(2),
            },
        ],
    };
    let mut ints = Vec::new();
    e.for_each_recursive(|n| {
        if let PureExpr::Int(v) = n {
            ints.push(*v);
        }
    });
    assert_eq!(ints, vec![1, 2]);
}

#[test]
fn for_each_recursive_logic_fn_call() {
    let e = PureExpr::LogicFnCall {
        name: "fn_name".to_string(),
        args: vec![int(10), int(20)],
    };
    let mut ints = Vec::new();
    e.for_each_recursive(|n| {
        if let PureExpr::Int(v) = n {
            ints.push(*v);
        }
    });
    assert_eq!(ints, vec![10, 20]);
}

#[test]
fn for_each_recursive_let_assume_obligation() {
    let e = PureExpr::LetAssume {
        assumption: arc(PureExpr::Bool(true)),
        body: arc(PureExpr::LetObligation {
            obligation: arc(PureExpr::Bool(false)),
            body: arc(int(42)),
        }),
    };
    let mut count = 0;
    e.for_each_recursive(|_| count += 1);
    // LetAssume + Bool(true) + LetObligation + Bool(false) + Int(42) = 5
    assert_eq!(count, 5);
}

// ════════════════════════════════════════════════════════════════════
// rewrite_bottom_up
// ════════════════════════════════════════════════════════════════════

#[test]
fn rewrite_bottom_up_identity() {
    let e = add(int(1), int(2));
    let result = e.rewrite_bottom_up(|n| n);
    assert_eq!(result, e);
}

#[test]
fn rewrite_bottom_up_replaces_leaf() {
    let e = add(var("x"), int(1));
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Var(ref name, _) if name == "x" => int(99),
        other => other,
    });
    assert_eq!(result, add(int(99), int(1)));
}

#[test]
fn rewrite_bottom_up_order_children_before_parent() {
    // Rewrite Int(1) -> Int(10), then check that the BinOp sees the rewritten children
    let e = add(int(1), int(1));
    let mut rewrite_log = Vec::new();
    let result = e.rewrite_bottom_up(|n| {
        match &n {
            PureExpr::Int(1) => {
                rewrite_log.push("leaf");
                int(10)
            }
            PureExpr::BinOp(left, _, right) => {
                // At this point, children should already be rewritten
                rewrite_log.push("parent");
                assert_eq!(
                    left.as_ref(),
                    &int(10),
                    "left child should already be rewritten"
                );
                assert_eq!(
                    right.as_ref(),
                    &int(10),
                    "right child should already be rewritten"
                );
                n
            }
            _ => n,
        }
    });
    assert_eq!(rewrite_log, vec!["leaf", "leaf", "parent"]);
    assert_eq!(result, add(int(10), int(10)));
}

#[test]
fn rewrite_bottom_up_unop() {
    let e = PureExpr::UnOp(UnOp::Neg, arc(int(5)));
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(5) => int(10),
        other => other,
    });
    assert_eq!(result, PureExpr::UnOp(UnOp::Neg, arc(int(10))));
}

#[test]
fn rewrite_bottom_up_ite() {
    let e = PureExpr::Ite(arc(PureExpr::Bool(true)), arc(int(1)), arc(int(2)));
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(v) => int(v * 10),
        other => other,
    });
    assert_eq!(
        result,
        PureExpr::Ite(arc(PureExpr::Bool(true)), arc(int(10)), arc(int(20)))
    );
}

#[test]
fn rewrite_bottom_up_old() {
    let e = PureExpr::Old(arc(var("x")));
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Var(ref name, _) if name == "x" => var("y"),
        other => other,
    });
    assert_eq!(result, PureExpr::Old(arc(var("y"))));
}

#[test]
fn rewrite_bottom_up_deref() {
    let e = PureExpr::Deref(arc(var("p")));
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Var(ref name, _) if name == "p" => var("q"),
        other => other,
    });
    assert_eq!(result, PureExpr::Deref(arc(var("q"))));
}

#[test]
fn rewrite_bottom_up_final() {
    let e = PureExpr::Final(arc(var("f")));
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Var(ref name, _) if name == "f" => var("g"),
        other => other,
    });
    assert_eq!(result, PureExpr::Final(arc(var("g"))));
}

#[test]
fn rewrite_bottom_up_view() {
    let e = PureExpr::View(arc(var("v")));
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Var(ref name, _) if name == "v" => var("w"),
        other => other,
    });
    assert_eq!(result, PureExpr::View(arc(var("w"))));
}

#[test]
fn rewrite_bottom_up_method_call() {
    let e = PureExpr::MethodCall {
        receiver: arc(var("r")),
        method: "m".to_string(),
        args: vec![int(1)],
    };
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(1) => int(100),
        PureExpr::Var(ref name, _) if name == "r" => var("s"),
        other => other,
    });
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: arc(var("s")),
            method: "m".to_string(),
            args: vec![int(100)],
        }
    );
}

#[test]
fn rewrite_bottom_up_forall_body_and_triggers() {
    let e = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: arc(int(1)),
        triggers: vec![vec![int(2)]],
    };
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(v) => int(v * 10),
        other => other,
    });
    match &result {
        PureExpr::Forall { body, triggers, .. } => {
            assert_eq!(body.as_ref(), &int(10));
            assert_eq!(triggers[0][0], int(20));
        }
        _ => panic!("expected Forall"),
    }
}

#[test]
fn rewrite_bottom_up_exists_body_and_triggers() {
    let e = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: arc(int(3)),
        triggers: vec![vec![int(4), int(5)]],
    };
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(v) => int(v + 100),
        other => other,
    });
    match &result {
        PureExpr::Exists { body, triggers, .. } => {
            assert_eq!(body.as_ref(), &int(103));
            assert_eq!(triggers[0][0], int(104));
            assert_eq!(triggers[0][1], int(105));
        }
        _ => panic!("expected Exists"),
    }
}

#[test]
fn rewrite_bottom_up_match_scrutinee_and_arms() {
    let e = PureExpr::Match {
        scrutinee: arc(var("s")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: int(7),
        }],
    };
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(7) => int(77),
        PureExpr::Var(ref name, _) if name == "s" => var("t"),
        other => other,
    });
    match &result {
        PureExpr::Match { scrutinee, arms } => {
            assert_eq!(scrutinee.as_ref(), &var("t"));
            assert_eq!(arms[0].body, int(77));
        }
        _ => panic!("expected Match"),
    }
}

#[test]
fn rewrite_bottom_up_logic_fn_call() {
    let e = PureExpr::LogicFnCall {
        name: "foo".to_string(),
        args: vec![int(1), int(2)],
    };
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(v) => int(v * 3),
        other => other,
    });
    match &result {
        PureExpr::LogicFnCall { args, .. } => {
            assert_eq!(args, &[int(3), int(6)]);
        }
        _ => panic!("expected LogicFnCall"),
    }
}

#[test]
fn rewrite_bottom_up_let() {
    let e = PureExpr::Let {
        var: "x".to_string(),
        value: arc(int(1)),
        body: arc(int(2)),
    };
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(v) => int(v + 10),
        other => other,
    });
    match &result {
        PureExpr::Let { value, body, .. } => {
            assert_eq!(value.as_ref(), &int(11));
            assert_eq!(body.as_ref(), &int(12));
        }
        _ => panic!("expected Let"),
    }
}

#[test]
fn rewrite_bottom_up_let_assume() {
    let e = PureExpr::LetAssume {
        assumption: arc(PureExpr::Bool(true)),
        body: arc(int(5)),
    };
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(5) => int(50),
        other => other,
    });
    match &result {
        PureExpr::LetAssume { body, .. } => {
            assert_eq!(body.as_ref(), &int(50));
        }
        _ => panic!("expected LetAssume"),
    }
}

#[test]
fn rewrite_bottom_up_let_obligation() {
    let e = PureExpr::LetObligation {
        obligation: arc(int(1)),
        body: arc(int(2)),
    };
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(v) => int(v * 100),
        other => other,
    });
    match &result {
        PureExpr::LetObligation {
            obligation, body, ..
        } => {
            assert_eq!(obligation.as_ref(), &int(100));
            assert_eq!(body.as_ref(), &int(200));
        }
        _ => panic!("expected LetObligation"),
    }
}

#[test]
fn rewrite_bottom_up_closure() {
    let e = PureExpr::Closure {
        params: vec![("p".to_string(), Some(ExprSort::Int))],
        body: arc(int(9)),
    };
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Int(9) => int(99),
        other => other,
    });
    match &result {
        PureExpr::Closure { params, body } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].0, "p");
            assert_eq!(body.as_ref(), &int(99));
        }
        _ => panic!("expected Closure"),
    }
}

#[test]
fn rewrite_bottom_up_structural_sharing_identity() {
    // When rewrite is identity, Arc pointers should be reused
    let shared = arc(int(42));
    let e = PureExpr::BinOp(Arc::clone(&shared), BinOp::Add, Arc::clone(&shared));
    let result = e.rewrite_bottom_up(|n| n);
    if let PureExpr::BinOp(left, _, right) = &result {
        assert!(
            Arc::ptr_eq(left, &shared),
            "identity rewrite should reuse Arc pointer for left"
        );
        assert!(
            Arc::ptr_eq(right, &shared),
            "identity rewrite should reuse Arc pointer for right"
        );
    } else {
        panic!("expected BinOp");
    }
}

#[test]
fn rewrite_bottom_up_float_passthrough() {
    let e = PureExpr::Float(FloatBits::from_f64(2.718));
    let result = e.rewrite_bottom_up(|n| n);
    assert_eq!(result, e);
}

#[test]
fn rewrite_bottom_up_nested_deep_tree() {
    // Build: Old(Deref(Final(View(x)))) and rename x -> y
    let e = PureExpr::Old(arc(PureExpr::Deref(arc(PureExpr::Final(arc(
        PureExpr::View(arc(var("x"))),
    ))))));
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::Var(ref name, _) if name == "x" => var("y"),
        other => other,
    });
    let expected = PureExpr::Old(arc(PureExpr::Deref(arc(PureExpr::Final(arc(
        PureExpr::View(arc(var("y"))),
    ))))));
    assert_eq!(result, expected);
}

#[test]
fn rewrite_bottom_up_can_replace_parent_after_children() {
    // Replace all BinOps with their left child (after children are rewritten)
    let e = add(add(int(1), int(2)), int(3));
    let result = e.rewrite_bottom_up(|n| match n {
        PureExpr::BinOp(left, _, _) => left.as_ref().clone(),
        other => other,
    });
    // Inner BinOp(1,2) -> 1, outer BinOp(1,3) -> 1
    assert_eq!(result, int(1));
}
