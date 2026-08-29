// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

use super::{
    datatype_var, int_var, into_iter_var, is_into_iter_receiver, make_completed, make_produces,
    make_produces_back, option_into_iter_var, rewrite_expr, seq_var, wrapped_receiver,
};

#[test]
fn test_into_iter_receiver_detected() {
    assert!(is_into_iter_receiver(&into_iter_var("it")));
}

#[test]
fn test_into_iter_receiver_through_deref() {
    let expr = PureExpr::Deref(Arc::new(into_iter_var("self")));
    assert!(is_into_iter_receiver(&expr));
}

#[test]
fn test_non_into_iter_receiver_rejected() {
    assert!(!is_into_iter_receiver(&int_var("x")));
}

#[test]
fn test_non_vec_into_iter_receiver_rejected() {
    assert!(!is_into_iter_receiver(&option_into_iter_var("it")));
}

#[test]
fn test_unsorted_var_rejected() {
    assert!(!is_into_iter_receiver(&PureExpr::Var(
        "it".to_string(),
        None,
    )));
}

#[test]
fn test_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        into_iter_var("it"),
        seq_var("visited"),
        into_iter_var("next"),
    ));
    let PureExpr::MethodCall {
        method,
        receiver,
        args,
    } = &rewritten
    else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "ext_eq");
    assert!(matches!(receiver.as_ref(), PureExpr::View(_)));
    assert_eq!(args.len(), 1);
    let PureExpr::MethodCall {
        method: concat_m,
        args: concat_a,
        ..
    } = &args[0]
    else {
        panic!("expected concat, got {:?}", args[0]);
    };
    assert_eq!(concat_m, "concat");
    assert_eq!(concat_a.len(), 1);
    assert!(matches!(&concat_a[0], PureExpr::View(_)));
}

#[test]
fn test_std_into_iter_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        datatype_var("it", "std::vec::IntoIter"),
        seq_var("visited"),
        datatype_var("next", "std::vec::IntoIter"),
    ));
    let PureExpr::MethodCall { method, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "ext_eq");
}

#[test]
fn test_into_iter_produces_rewrite_through_old_final_view() {
    let rewritten = rewrite_expr(&make_produces(
        wrapped_receiver(into_iter_var("it")),
        seq_var("visited"),
        into_iter_var("next"),
    ));
    let PureExpr::MethodCall {
        method, receiver, ..
    } = &rewritten
    else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "ext_eq");
    assert!(matches!(receiver.as_ref(), PureExpr::View(inner)
            if matches!(inner.as_ref(), PureExpr::Final(inner)
                if matches!(inner.as_ref(), PureExpr::View(inner)
                    if matches!(inner.as_ref(), PureExpr::Old(inner)
                        if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "it"))))));
}

#[test]
fn test_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(into_iter_var("it")));
    let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::Eq);
    assert!(matches!(rhs.as_ref(), PureExpr::Int(0)));
    let PureExpr::MethodCall {
        method, receiver, ..
    } = lhs.as_ref()
    else {
        panic!("expected len, got {lhs:?}");
    };
    assert_eq!(method, "len");
    assert!(matches!(receiver.as_ref(), PureExpr::View(_)));
}

#[test]
fn test_non_into_iter_produces_unchanged() {
    let rewritten = rewrite_expr(&make_produces(
        PureExpr::Var("it".to_string(), None),
        seq_var("visited"),
        PureExpr::Var("next".to_string(), None),
    ));
    let PureExpr::MethodCall { method, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "produces");
}

#[test]
fn test_slice_iter_produces_unchanged() {
    let id = intern_sort_name("core::slice::iter::Iter");
    let rewritten = rewrite_expr(&make_produces(
        PureExpr::Var("it".to_string(), Some(ExprSort::Datatype(id))),
        seq_var("visited"),
        PureExpr::Var("next".to_string(), Some(ExprSort::Datatype(id))),
    ));
    let PureExpr::MethodCall { method, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "produces");
}

#[test]
fn test_non_vec_into_iter_produces_unchanged() {
    let rewritten = rewrite_expr(&make_produces(
        option_into_iter_var("it"),
        seq_var("visited"),
        option_into_iter_var("next"),
    ));
    let PureExpr::MethodCall { method, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "produces");
}

// --- Logical SeqIter tests ---

#[test]
fn test_seq_iter_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        datatype_var("it", "trust_wp_std::logic::seq::SeqIter"),
        seq_var("visited"),
        datatype_var("next", "trust_wp_std::logic::seq::SeqIter"),
    ));
    let PureExpr::MethodCall { method, .. } = &rewritten else {
        panic!("expected ext_eq MethodCall, got {rewritten:?}");
    };
    assert_eq!(
        method, "ext_eq",
        "SeqIter should rewrite to Seq ext_eq(concat)"
    );
}

#[test]
fn test_seq_iter_all_sort_aliases() {
    for sort_name in [
        "trust_wp_std::logic::seq::SeqIter",
        "creusot_std::logic::seq::Iter",
        "logic::seq::Iter",
    ] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("it", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        let PureExpr::MethodCall { method, .. } = &rewritten else {
            panic!("{sort_name}: expected ext_eq, got {rewritten:?}");
        };
        assert_eq!(method, "ext_eq", "{sort_name} should rewrite to ext_eq");
    }
}

#[test]
fn test_seq_iter_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(datatype_var(
        "it",
        "trust_wp_std::logic::seq::SeqIter",
    )));
    let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::Eq);
    assert!(matches!(rhs.as_ref(), PureExpr::Int(0)));
    let PureExpr::MethodCall { method, .. } = lhs.as_ref() else {
        panic!("expected len, got {lhs:?}");
    };
    assert_eq!(method, "len");
}

// --- produces_back tests (#2217) ---

#[test]
fn test_into_iter_produces_back_rewrite() {
    let rewritten = rewrite_expr(&make_produces_back(
        into_iter_var("it"),
        seq_var("visited"),
        into_iter_var("next"),
    ));
    // Should rewrite to: it@.ext_eq(next@.concat(visited.reverse()))
    let PureExpr::MethodCall {
        method,
        receiver,
        args,
    } = &rewritten
    else {
        panic!("expected ext_eq MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "ext_eq");
    assert!(matches!(receiver.as_ref(), PureExpr::View(_)));
    assert_eq!(args.len(), 1);

    // The arg should be: next@.concat(visited.reverse())
    let PureExpr::MethodCall {
        method: concat_m,
        receiver: concat_recv,
        args: concat_a,
    } = &args[0]
    else {
        panic!("expected concat, got {:?}", args[0]);
    };
    assert_eq!(concat_m, "concat");
    assert!(matches!(concat_recv.as_ref(), PureExpr::View(_)));
    assert_eq!(concat_a.len(), 1);

    // The concat arg should be: visited.reverse()
    let PureExpr::MethodCall {
        method: rev_m,
        args: rev_a,
        ..
    } = &concat_a[0]
    else {
        panic!("expected reverse, got {:?}", concat_a[0]);
    };
    assert_eq!(rev_m, "reverse");
    assert!(rev_a.is_empty());
}

#[test]
fn test_non_into_iter_produces_back_unchanged() {
    let rewritten = rewrite_expr(&make_produces_back(
        PureExpr::Var("it".to_string(), None),
        seq_var("visited"),
        PureExpr::Var("next".to_string(), None),
    ));
    let PureExpr::MethodCall { method, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(
        method, "produces_back",
        "unsupported type should pass through"
    );
}
