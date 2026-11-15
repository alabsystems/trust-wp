// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr};

use crate::callbacks::closure_enrichment::{enrich_existential_body_for_test, ClosureEnsuresEntry};

fn postcondition_mut_call(receiver_name: &str) -> PureExpr {
    postcondition_mut_call_with_receiver(PureExpr::Var(receiver_name.to_string(), None))
}

fn postcondition_mut_call_with_receiver(receiver: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("args".to_string(), None),
            PureExpr::Var("st".to_string(), None),
            PureExpr::Var("res".to_string(), None),
        ],
    }
}

fn postcondition_once_call_with_receiver(receiver: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "postcondition_once".to_string(),
        args: vec![
            PureExpr::Var("args".to_string(), None),
            PureExpr::Var("res".to_string(), None),
        ],
    }
}

fn result_equals(value: i64) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(value)),
    )
}

/// A call-site assumption arrives as `precondition ==> exists<st, r>
/// postcondition_mut(..)`: the existential in the consequent is enriched, the
/// antecedent is left alone.
#[test]
fn enrich_existential_body_reaches_the_consequent_of_a_precondition_guard() {
    let guard = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c1".to_string(), None)),
        method: "precondition".to_string(),
        args: vec![PureExpr::Var("args".to_string(), None)],
    };
    let mut expr = PureExpr::BinOp(
        Arc::new(guard.clone()),
        BinOp::Implies,
        Arc::new(PureExpr::Exists {
            var: "st".to_string(),
            var_sort: None,
            body: Arc::new(postcondition_mut_call("c1")),
            triggers: vec![],
        }),
    );
    let closure_ensures = vec![ClosureEnsuresEntry {
        receiver_name: "c1".to_string(),
        param_names: vec![],
        capture_bindings: vec![],
        ensures_exprs: vec![result_equals(7)],
        env_arity: None,
    }];

    assert!(enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));
    let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = &expr else {
        panic!("the implication shape is kept: {expr:?}");
    };
    assert_eq!(antecedent.as_ref(), &guard, "the antecedent is untouched");
    let PureExpr::Exists { body, .. } = consequent.as_ref() else {
        panic!("the existential is kept: {consequent:?}");
    };
    let PureExpr::BinOp(original, BinOp::And, injected) = body.as_ref() else {
        panic!("the concrete ensures is conjoined inside the existential: {body:?}");
    };
    assert_eq!(original.as_ref(), &postcondition_mut_call("c1"));
    assert!(
        format!("{injected:?}").contains("Int(7)"),
        "the closure's ensures is the injected conjunct: {injected:?}"
    );
}

#[test]
fn enrich_existential_body_uses_matching_receiver_instead_of_first_entry() {
    let mut expr = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(postcondition_mut_call("c2")),
        triggers: vec![],
    };
    let closure_ensures = vec![
        ClosureEnsuresEntry {
            receiver_name: "c1".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(1)],
            env_arity: None,
        },
        ClosureEnsuresEntry {
            receiver_name: "c2".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(2)],
            env_arity: None,
        },
    ];

    assert!(enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));

    let expected = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(postcondition_mut_call("c2")),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("res".to_string(), None)),
                BinOp::Eq,
                Arc::new(PureExpr::Int(2)),
            )),
        )),
        triggers: vec![],
    };
    assert_eq!(expr, expected);
}

#[test]
fn enrich_existential_body_ambiguous_receiver_fails_closed() {
    let original = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(postcondition_mut_call("c")),
        triggers: vec![],
    };
    let mut expr = original.clone();
    let closure_ensures = vec![
        ClosureEnsuresEntry {
            receiver_name: "c".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(1)],
            env_arity: None,
        },
        ClosureEnsuresEntry {
            receiver_name: "c".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(2)],
            env_arity: None,
        },
    ];

    assert!(!enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));
    assert_eq!(expr, original);
}

#[test]
fn enrich_existential_body_matches_wrapped_postcondition_once_receiver() {
    let receiver = PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "c2".to_string(),
        None,
    )))));
    let mut expr = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(postcondition_once_call_with_receiver(receiver.clone())),
        triggers: vec![],
    };
    let closure_ensures = vec![ClosureEnsuresEntry {
        receiver_name: "c2".to_string(),
        param_names: vec![],
        capture_bindings: vec![],
        ensures_exprs: vec![result_equals(2)],
        env_arity: None,
    }];

    assert!(enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));

    let expected = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(postcondition_once_call_with_receiver(receiver)),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("res".to_string(), None)),
                BinOp::Eq,
                Arc::new(PureExpr::Int(2)),
            )),
        )),
        triggers: vec![],
    };
    assert_eq!(expr, expected);
}

/// Identity or nothing (D-30): a receiver naming NO entry gets nothing even
/// when exactly one entry exists. A single-entry fallback would give
/// `c2 = |_| 2`'s call `c1`'s `result == 1` (adversarial
/// `s71_closure_ensures_sibling_fallback_*`).
#[test]
fn enrich_existential_body_refuses_unmatched_receiver_with_single_entry() {
    let original = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(postcondition_mut_call("c2")),
        triggers: vec![],
    };
    let mut expr = original.clone();
    let closure_ensures = vec![ClosureEnsuresEntry {
        receiver_name: "c1".to_string(),
        param_names: vec![],
        capture_bindings: vec![],
        ensures_exprs: vec![result_equals(1)],
        env_arity: None,
    }];

    assert!(!enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));
    assert_eq!(expr, original);
}

/// A tuple-constructor receiver is the lowered capture environment of SOME
/// closure — two capture-less closures share `__trust_wp_tuple0()` — so
/// unless the driver recorded an entry as the sole owner of that arity
/// (`env_arity`) it identifies none of them: nothing is injected, single
/// entry or not.
#[test]
fn enrich_existential_body_refuses_tuple_constructor_receiver_without_owner() {
    let receiver = PureExpr::Deref(Arc::new(PureExpr::Final(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple0".to_string(),
        args: vec![],
    }))));
    let original = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(postcondition_mut_call_with_receiver(receiver)),
        triggers: vec![],
    };
    let mut expr = original.clone();
    let closure_ensures = vec![ClosureEnsuresEntry {
        receiver_name: "c1".to_string(),
        param_names: vec![],
        capture_bindings: vec![],
        ensures_exprs: vec![result_equals(1)],
        env_arity: None,
    }];

    assert!(!enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));
    assert_eq!(expr, original);
}

/// A chained FnMut call keeps its identity through the state variable: in
/// `exists<st1, st2> c.postcondition_mut(a, st1, r1) && st1.postcondition_mut(a, st2, r2)`
/// the second receiver `st1` is the state `c`'s call produced, so `c`'s
/// ensures is injected at BOTH calls — and only `c`'s.
#[test]
fn enrich_existential_body_follows_state_variable_to_its_producer() {
    let first = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("c".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("a".to_string(), None),
            PureExpr::Var("st1".to_string(), None),
            PureExpr::Var("r1".to_string(), None),
        ],
    };
    let second = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("st1".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("a".to_string(), None),
            PureExpr::Var("st2".to_string(), None),
            PureExpr::Var("r2".to_string(), None),
        ],
    };
    // The chain is written second-call-first: resolution must not depend on order.
    let mut expr = PureExpr::Exists {
        var: "st1".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Exists {
            var: "st2".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(second.clone()),
                BinOp::And,
                Arc::new(first.clone()),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };
    let closure_ensures = vec![
        ClosureEnsuresEntry {
            receiver_name: "c".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(7)],
            env_arity: None,
        },
        ClosureEnsuresEntry {
            receiver_name: "other".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(9)],
            env_arity: None,
        },
    ];

    assert!(enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));
    let PureExpr::Exists { body: outer, .. } = &expr else {
        panic!("outer exists kept: {expr:?}");
    };
    let PureExpr::Exists { body: inner, .. } = outer.as_ref() else {
        panic!("inner exists kept: {outer:?}");
    };
    let PureExpr::BinOp(left, BinOp::And, right) = inner.as_ref() else {
        panic!("conjunction kept: {inner:?}");
    };
    for (call, original) in [(left, &second), (right, &first)] {
        let PureExpr::BinOp(kept, BinOp::And, injected) = call.as_ref() else {
            panic!("call enriched: {call:?}");
        };
        assert_eq!(kept.as_ref(), original);
        let shown = format!("{injected:?}");
        assert!(shown.contains("Int(7)"), "c's ensures injected: {shown}");
        assert!(
            !shown.contains("Int(9)"),
            "other's ensures NOT injected: {shown}"
        );
    }
}

/// A state variable whose producing call has no identity (a tuple-constructor
/// receiver) owns nothing: the chained call on it gets nothing too.
#[test]
fn enrich_existential_body_state_of_unidentified_producer_gets_nothing() {
    let first = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple1".to_string(),
            args: vec![PureExpr::Int(0)],
        }))),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("a".to_string(), None),
            PureExpr::Var("st1".to_string(), None),
            PureExpr::Var("r1".to_string(), None),
        ],
    };
    let second = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("st1".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("a".to_string(), None),
            PureExpr::Var("st2".to_string(), None),
            PureExpr::Var("r2".to_string(), None),
        ],
    };
    let original = PureExpr::Exists {
        var: "st1".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Exists {
            var: "st2".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(first),
                BinOp::And,
                Arc::new(second),
            )),
            triggers: vec![],
        }),
        triggers: vec![],
    };
    let mut expr = original.clone();
    let closure_ensures = vec![ClosureEnsuresEntry {
        receiver_name: "c".to_string(),
        param_names: vec![],
        capture_bindings: vec![],
        ensures_exprs: vec![result_equals(7)],
        env_arity: None,
    }];

    assert!(!enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));
    assert_eq!(expr, original);
}

/// An existential binder shadows a source local of the same name: `st` in
/// `exists<st> ..` is never the closure `let st = ..` binds.
#[test]
fn enrich_existential_body_bound_name_is_not_a_source_local() {
    let original = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("st".to_string(), None)),
            method: "postcondition_mut".to_string(),
            args: vec![
                PureExpr::Var("a".to_string(), None),
                PureExpr::Var("st2".to_string(), None),
                PureExpr::Var("r".to_string(), None),
            ],
        }),
        triggers: vec![],
    };
    let mut expr = original.clone();
    let closure_ensures = vec![ClosureEnsuresEntry {
        receiver_name: "st".to_string(),
        param_names: vec![],
        capture_bindings: vec![],
        ensures_exprs: vec![result_equals(7)],
        env_arity: None,
    }];

    assert!(!enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));
    assert_eq!(expr, original);
}

/// The entry the driver recorded as the SOLE owner of an environment arity
/// (`env_arity`) is injected at a `__trust_wp_tuple<N>(..)` receiver of that
/// arity — and an entry of another arity is not.
#[test]
fn enrich_existential_body_injects_sole_arity_owner_at_env_constructor_receiver() {
    let receiver = PureExpr::Deref(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple1".to_string(),
        args: vec![PureExpr::Int(0)],
    }));
    let mut expr = PureExpr::Exists {
        var: "st".to_string(),
        var_sort: None,
        body: Arc::new(postcondition_mut_call_with_receiver(receiver.clone())),
        triggers: vec![],
    };
    let closure_ensures = vec![
        ClosureEnsuresEntry {
            receiver_name: "c".to_string(),
            param_names: vec![],
            capture_bindings: vec![(0, "x".to_string())],
            ensures_exprs: vec![result_equals(3)],
            env_arity: Some(1),
        },
        ClosureEnsuresEntry {
            receiver_name: "d".to_string(),
            param_names: vec![],
            capture_bindings: vec![],
            ensures_exprs: vec![result_equals(4)],
            env_arity: Some(0),
        },
    ];

    assert!(enrich_existential_body_for_test(
        &mut expr,
        &closure_ensures
    ));
    let PureExpr::Exists { body, .. } = &expr else {
        panic!("the existential is kept: {expr:?}");
    };
    let PureExpr::BinOp(original, BinOp::And, injected) = body.as_ref() else {
        panic!("the concrete ensures is conjoined: {body:?}");
    };
    assert_eq!(
        original.as_ref(),
        &postcondition_mut_call_with_receiver(receiver)
    );
    let shown = format!("{injected:?}");
    assert!(shown.contains("Int(3)"), "c's ensures injected: {shown}");
    assert!(
        !shown.contains("Int(4)"),
        "d's ensures not injected: {shown}"
    );
}
