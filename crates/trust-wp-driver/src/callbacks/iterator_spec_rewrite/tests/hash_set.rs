// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

use super::{
    datatype_var, flattened_and_clauses, hash_set_into_iter_var, hash_set_iter_var, make_completed,
    make_produces, rewrite_expr, seq_var, wrapped_receiver,
};

fn assert_length_partition_clause(clause: &PureExpr, receiver_name: &str, next_name: &str) {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = clause else {
        panic!("expected length partition equality, got {clause:?}");
    };
    assert!(
        matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
            if method == "len"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == receiver_name)))
    );
    assert!(matches!(rhs.as_ref(), PureExpr::BinOp(lhs, BinOp::Add, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::View(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == next_name)))));
}

fn assert_hash_set_partition_clauses(clauses: &[&PureExpr]) {
    let [len_clause, visited_clause, next_clause, receiver_clause, uniqueness_clause] = clauses
    else {
        panic!("expected five top-level clauses, got {clauses:?}");
    };

    assert_length_partition_clause(len_clause, "it", "next");

    // Visited clause: forall __hash_set_visited_elem: contains(visited, elem) ==>
    //   contains(it@, deep_model(elem)) && !contains(next@, deep_model(elem))
    let PureExpr::Forall {
        var,
        body,
        triggers,
        ..
    } = visited_clause
    else {
        panic!("expected visited-elem forall, got {visited_clause:?}");
    };
    assert_eq!(var, "__hash_set_visited_elem");
    assert_eq!(triggers.len(), 1);
    assert!(matches!(&triggers[0][0], PureExpr::MethodCall { method, .. } if method == "contains"));
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Implies, rhs)
        if matches!(rhs.as_ref(), PureExpr::BinOp(_, BinOp::And, rhs)
            if matches!(rhs.as_ref(), PureExpr::UnOp(UnOp::Not, _))))
    );

    // Next clause: forall __hash_set_next_dm: contains(next@, dm) ==>
    //   contains(it@, dm) && !exists witness: ...
    let PureExpr::Forall {
        var,
        body,
        triggers,
        ..
    } = next_clause
    else {
        panic!("expected next-dm forall, got {next_clause:?}");
    };
    assert_eq!(var, "__hash_set_next_dm");
    assert_eq!(triggers.len(), 1);
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Implies, rhs)
        if matches!(rhs.as_ref(), PureExpr::BinOp(_, BinOp::And, rhs)
            if matches!(rhs.as_ref(), PureExpr::UnOp(UnOp::Not, inner)
                if matches!(inner.as_ref(), PureExpr::Exists { var, .. } if var == "__hash_set_next_witness"))))
    );

    // Receiver clause: forall __hash_set_receiver_dm: contains(it@, dm) ==>
    //   contains(next@, dm) || exists witness: ...
    let PureExpr::Forall {
        var,
        body,
        triggers,
        ..
    } = receiver_clause
    else {
        panic!("expected receiver-dm forall, got {receiver_clause:?}");
    };
    assert_eq!(var, "__hash_set_receiver_dm");
    assert_eq!(triggers.len(), 1);
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Implies, rhs)
        if matches!(rhs.as_ref(), PureExpr::BinOp(_, BinOp::Or, rhs)
            if matches!(rhs.as_ref(), PureExpr::Exists { var, .. } if var == "__hash_set_cover_witness")))
    );

    // Uniqueness clause: nested forall over visited_elem_1, visited_elem_2
    let PureExpr::Forall {
        var,
        body,
        triggers,
        ..
    } = uniqueness_clause
    else {
        panic!("expected uniqueness forall, got {uniqueness_clause:?}");
    };
    assert_eq!(var, "__hash_set_visited_elem_1");
    assert_eq!(triggers.len(), 1);
    let PureExpr::Forall {
        var,
        body,
        triggers,
        ..
    } = body.as_ref()
    else {
        panic!("expected nested forall, got {body:?}");
    };
    assert_eq!(var, "__hash_set_visited_elem_2");
    assert_eq!(triggers.len(), 1);
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Implies, rhs)
        if matches!(rhs.as_ref(), PureExpr::BinOp(_, BinOp::Eq, _)))
    );
}

#[test]
fn test_hash_set_into_iter_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        hash_set_into_iter_var("it"),
        seq_var("visited"),
        hash_set_into_iter_var("next"),
    ));
    assert_hash_set_partition_clauses(&flattened_and_clauses(&rewritten));
}

#[test]
fn test_hash_set_iter_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        hash_set_iter_var("it"),
        seq_var("visited"),
        hash_set_iter_var("next"),
    ));
    assert_hash_set_partition_clauses(&flattened_and_clauses(&rewritten));
}

#[test]
fn test_hash_set_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(hash_set_into_iter_var("it")));
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = &rewritten
    else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "is_empty");
    assert!(args.is_empty());
    assert!(matches!(receiver.as_ref(), PureExpr::View(inner)
            if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "it")));
}

#[test]
fn test_hash_set_completed_rewrite_through_wrappers() {
    let rewritten = rewrite_expr(&make_completed(wrapped_receiver(hash_set_iter_var("it"))));
    let PureExpr::MethodCall { method, args, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "is_empty");
    assert!(args.is_empty());
}

#[test]
fn test_hash_set_produces_rewrite_alias_sorts() {
    for sort_name in [
        "std::collections::hash::set::IntoIter",
        "std::collections::hash::set::Iter",
    ] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("it", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        assert_eq!(
            flattened_and_clauses(&rewritten).len(),
            5,
            "{sort_name} should rewrite to the five-clause partition formula"
        );
    }
}

#[test]
fn test_hash_set_intersection_and_difference_rewrite_alias_sorts() {
    for sort_name in [
        "std::collections::hash::set::Intersection",
        "std::collections::hash::set::Difference",
    ] {
        let rewritten = rewrite_expr(&make_completed(datatype_var("it", sort_name)));
        let PureExpr::MethodCall { method, args, .. } = &rewritten else {
            panic!("expected MethodCall, got {rewritten:?}");
        };
        assert_eq!(method, "is_empty");
        assert!(args.is_empty());
    }
}

#[test]
fn test_logical_fset_iter_produces_unchanged() {
    let rewritten = rewrite_expr(&make_produces(
        datatype_var("it", "logic::fset::Iter"),
        seq_var("visited"),
        datatype_var("next", "logic::fset::Iter"),
    ));
    let PureExpr::MethodCall { method, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "produces");
}

// ── Error-path and boundary tests ─────────────────────────────────────

/// Wrong-arity `produces` (0 args) on HashSet IntoIter is NOT rewritten.
/// `rewrite_hash_set_produces` returns None when args.len() != 2.
#[test]
fn test_hash_set_produces_wrong_arity_zero_args_unchanged() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(hash_set_into_iter_var("it")),
        method: "produces".to_string(),
        args: vec![],
    };
    let rewritten = rewrite_expr(&expr);
    let PureExpr::MethodCall { method, args, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "produces");
    assert!(
        args.is_empty(),
        "zero-arg produces should be preserved unchanged"
    );
}

/// Wrong-arity `produces` (1 arg) on HashSet Iter is NOT rewritten.
#[test]
fn test_hash_set_produces_wrong_arity_one_arg_unchanged() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(hash_set_iter_var("it")),
        method: "produces".to_string(),
        args: vec![seq_var("visited")],
    };
    let rewritten = rewrite_expr(&expr);
    let PureExpr::MethodCall { method, args, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "produces");
    assert_eq!(
        args.len(),
        1,
        "one-arg produces should be preserved unchanged"
    );
}

/// Wrong-arity `produces` (3 args) on HashSet IntoIter is NOT rewritten.
#[test]
fn test_hash_set_produces_wrong_arity_three_args_unchanged() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(hash_set_into_iter_var("it")),
        method: "produces".to_string(),
        args: vec![
            seq_var("visited"),
            hash_set_into_iter_var("next"),
            PureExpr::Int(0),
        ],
    };
    let rewritten = rewrite_expr(&expr);
    let PureExpr::MethodCall { method, args, .. } = &rewritten else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "produces");
    assert_eq!(
        args.len(),
        3,
        "three-arg produces should be preserved unchanged"
    );
}

/// Unknown method on HashSet iterator is NOT rewritten.
/// Exercises the `_ => None` branch in `try_rewrite_collection_iter_method`.
#[test]
fn test_hash_set_unknown_method_unchanged() {
    for method_name in ["next", "size_hint", "count", "nth", "fold"] {
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(hash_set_into_iter_var("it")),
            method: method_name.to_string(),
            args: vec![],
        };
        let rewritten = rewrite_expr(&expr);
        let PureExpr::MethodCall { method, .. } = &rewritten else {
            panic!("expected MethodCall for {method_name}, got {rewritten:?}");
        };
        assert_eq!(
            method, method_name,
            "unknown method '{method_name}' on HashSet iterator should be preserved"
        );
    }
}

/// HashMap iterator is rewritten by the HashMap path, not the HashSet path.
/// Verify that HashMap produces uses `__hash_map_*` variables, not `__hash_set_*`.
#[test]
fn test_hash_map_iter_not_treated_as_hash_set() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(datatype_var("it", "std::collections::hash_map::IntoIter")),
        method: "produces".to_string(),
        args: vec![
            seq_var("visited"),
            datatype_var("next", "std::collections::hash_map::IntoIter"),
        ],
    };
    let rewritten = rewrite_expr(&expr);
    let debug_str = format!("{rewritten:?}");
    assert!(
        debug_str.contains("__hash_map_"),
        "HashMap IntoIter produces should use __hash_map_ variable prefix"
    );
    assert!(
        !debug_str.contains("__hash_set_"),
        "HashMap IntoIter produces should NOT use __hash_set_ variable prefix"
    );
}
