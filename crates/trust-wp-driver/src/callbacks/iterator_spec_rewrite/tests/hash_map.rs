// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_name, BinOp, ExprSort, PureExpr,
};

use super::{
    datatype_var, flattened_and_clauses, hash_map_into_iter_var, hash_map_iter_mut_var,
    hash_map_iter_var, make_completed, make_produces, rewrite_expr, seq_var, wrapped_receiver,
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

fn assert_hash_map_partition_clauses(clauses: &[&PureExpr]) {
    let [len_clause, visited_clause, next_clause, receiver_clause, uniqueness_clause] = clauses
    else {
        panic!("expected five top-level clauses, got {clauses:?}");
    };

    assert_length_partition_clause(len_clause, "it", "next");

    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = visited_clause
    else {
        panic!("expected visited-entry forall, got {visited_clause:?}");
    };
    assert_eq!(var, "__hash_map_visited_entry");
    assert_eq!(*var_sort, Some(ExprSort::Tuple(2)));
    assert_eq!(triggers.len(), 1);
    assert!(
        matches!(&triggers[0][0], PureExpr::MethodCall { method, receiver, args }
            if method == "contains"
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Tuple(2)))] if name == "__hash_map_visited_entry"))
    );
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Implies, rhs)
            if matches!(rhs.as_ref(), PureExpr::BinOp(_, BinOp::And, _)))
    );

    let PureExpr::Forall {
        var,
        var_sort,
        body,
        ..
    } = next_clause
    else {
        panic!("expected next-entry forall, got {next_clause:?}");
    };
    assert_eq!(var, "__hash_map_next_entry");
    assert_eq!(*var_sort, Some(ExprSort::Tuple(2)));
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Implies, rhs)
            if matches!(rhs.as_ref(), PureExpr::BinOp(_, BinOp::And, rhs)
                if matches!(rhs.as_ref(), PureExpr::UnOp(_, inner)
                    if matches!(inner.as_ref(), PureExpr::Exists { var, .. } if var == "__hash_map_next_witness"))))
    );

    let PureExpr::Forall {
        var,
        var_sort,
        body,
        ..
    } = receiver_clause
    else {
        panic!("expected receiver-entry forall, got {receiver_clause:?}");
    };
    assert_eq!(var, "__hash_map_receiver_entry");
    assert_eq!(*var_sort, Some(ExprSort::Tuple(2)));
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Implies, rhs)
            if matches!(rhs.as_ref(), PureExpr::BinOp(lhs, BinOp::Or, _)
                if matches!(lhs.as_ref(), PureExpr::Exists { var, .. } if var == "__hash_map_receiver_witness")))
    );

    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = uniqueness_clause
    else {
        panic!("expected uniqueness forall, got {uniqueness_clause:?}");
    };
    assert_eq!(var, "__hash_map_visited_entry_1");
    assert_eq!(*var_sort, Some(ExprSort::Tuple(2)));
    assert_eq!(triggers.len(), 1);
    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = body.as_ref()
    else {
        panic!("expected nested forall over visited entry 2, got {body:?}");
    };
    assert_eq!(var, "__hash_map_visited_entry_2");
    assert_eq!(*var_sort, Some(ExprSort::Tuple(2)));
    assert_eq!(triggers.len(), 1);
    assert!(
        matches!(&triggers[0][0], PureExpr::MethodCall { method, receiver, args }
            if method == "contains"
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Tuple(2)))] if name == "__hash_map_visited_entry_2"))
    );
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Implies, rhs)
            if matches!(rhs.as_ref(), PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                if matches!(lhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Tuple(2))) if name == "__hash_map_visited_entry_1")
                && matches!(rhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Tuple(2))) if name == "__hash_map_visited_entry_2")))
    );
}

fn assert_completed_is_empty(rewritten: &PureExpr, receiver_name: &str) {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = rewritten
    else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "is_empty");
    assert!(args.is_empty());
    assert!(matches!(receiver.as_ref(), PureExpr::View(inner)
            if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == receiver_name)));
}

fn assert_shared_iter_value_bridge(clause: &PureExpr, witness_name: &str, expect_deref: bool) {
    let value_expr = if witness_name == "__hash_map_visited_entry" {
        let PureExpr::Forall { body, .. } = clause else {
            panic!("expected forall clause, got {clause:?}");
        };
        let PureExpr::BinOp(_, BinOp::Implies, rhs) = body.as_ref() else {
            panic!("expected implication body, got {body:?}");
        };
        let PureExpr::BinOp(lhs, BinOp::And, _) = rhs.as_ref() else {
            panic!("expected top-level conjunction, got {rhs:?}");
        };
        let PureExpr::BinOp(_, BinOp::And, eq_clause) = lhs.as_ref() else {
            panic!("expected nested conjunction, got {lhs:?}");
        };
        let PureExpr::BinOp(_, BinOp::Eq, value_expr) = eq_clause.as_ref() else {
            panic!("expected value equality, got {eq_clause:?}");
        };
        value_expr.as_ref()
    } else {
        let PureExpr::Forall { body, .. } = clause else {
            panic!("expected forall clause, got {clause:?}");
        };
        let PureExpr::BinOp(_, BinOp::Implies, rhs) = body.as_ref() else {
            panic!("expected implication body, got {body:?}");
        };
        let PureExpr::BinOp(lhs, BinOp::Or, _) = rhs.as_ref() else {
            panic!("expected or-branch body, got {rhs:?}");
        };
        let PureExpr::Exists { body, .. } = lhs.as_ref() else {
            panic!("expected visited-entry witness exists, got {lhs:?}");
        };
        let PureExpr::BinOp(_, BinOp::And, value_eq) = body.as_ref() else {
            panic!("expected witness conjunction, got {body:?}");
        };
        let PureExpr::BinOp(value_expr, BinOp::Eq, _) = value_eq.as_ref() else {
            panic!("expected witness value equality, got {value_eq:?}");
        };
        value_expr.as_ref()
    };

    let tuple_value_expr_matches = |expr: &PureExpr| {
        matches!(expr, PureExpr::LogicFnCall { name, args }
            if name == &tuple_field_logic_fn_name(1)
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Tuple(2)))] if name == witness_name))
    };

    if expect_deref {
        assert!(
            matches!(value_expr, PureExpr::Deref(inner) if tuple_value_expr_matches(inner)),
            "expected dereferenced tuple value for {witness_name}, got {value_expr:?}"
        );
    } else {
        assert!(
            tuple_value_expr_matches(value_expr),
            "expected raw tuple value for {witness_name}, got {value_expr:?}"
        );
    }
}

#[test]
fn test_hash_map_into_iter_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        hash_map_into_iter_var("it"),
        seq_var("visited"),
        hash_map_into_iter_var("next"),
    ));
    assert_hash_map_partition_clauses(&flattened_and_clauses(&rewritten));
}

#[test]
fn test_hash_map_iter_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        hash_map_iter_var("it"),
        seq_var("visited"),
        hash_map_iter_var("next"),
    ));
    assert_hash_map_partition_clauses(&flattened_and_clauses(&rewritten));
}

#[test]
fn test_hash_map_iter_mut_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        hash_map_iter_mut_var("it"),
        seq_var("visited"),
        hash_map_iter_mut_var("next"),
    ));
    assert_hash_map_partition_clauses(&flattened_and_clauses(&rewritten));
}

#[test]
fn test_hash_map_iter_rewrite_dereferences_shared_values() {
    let rewritten = rewrite_expr(&make_produces(
        hash_map_iter_var("it"),
        seq_var("visited"),
        hash_map_iter_var("next"),
    ));
    let clauses = flattened_and_clauses(&rewritten);
    let [_, visited_clause, _, receiver_clause, _] = clauses.as_slice() else {
        panic!("expected five clauses, got {clauses:?}");
    };
    assert_shared_iter_value_bridge(visited_clause, "__hash_map_visited_entry", true);
    assert_shared_iter_value_bridge(receiver_clause, "__hash_map_receiver_witness", true);
}

#[test]
fn test_hash_map_into_iter_rewrite_keeps_owned_values() {
    let rewritten = rewrite_expr(&make_produces(
        hash_map_into_iter_var("it"),
        seq_var("visited"),
        hash_map_into_iter_var("next"),
    ));
    let clauses = flattened_and_clauses(&rewritten);
    let [_, visited_clause, _, receiver_clause, _] = clauses.as_slice() else {
        panic!("expected five clauses, got {clauses:?}");
    };
    assert_shared_iter_value_bridge(visited_clause, "__hash_map_visited_entry", false);
    assert_shared_iter_value_bridge(receiver_clause, "__hash_map_receiver_witness", false);
}

#[test]
fn test_hash_map_iter_mut_rewrite_dereferences_mut_values() {
    let rewritten = rewrite_expr(&make_produces(
        hash_map_iter_mut_var("it"),
        seq_var("visited"),
        hash_map_iter_mut_var("next"),
    ));
    let clauses = flattened_and_clauses(&rewritten);
    let [_, visited_clause, _, receiver_clause, _] = clauses.as_slice() else {
        panic!("expected five clauses, got {clauses:?}");
    };
    // IterMut produces (&K, &mut V) — need Deref on &mut V to compare with FMap values
    assert_shared_iter_value_bridge(visited_clause, "__hash_map_visited_entry", true);
    assert_shared_iter_value_bridge(receiver_clause, "__hash_map_receiver_witness", true);
}

#[test]
fn test_hash_map_produces_rewrite_alias_sorts() {
    for sort_name in [
        "std::collections::hash::map::IntoIter",
        "std::collections::hash::map::Iter",
        "std::collections::hash::map::IterMut",
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
fn test_hash_map_completed_rewrite() {
    assert_completed_is_empty(
        &rewrite_expr(&make_completed(hash_map_iter_var("it"))),
        "it",
    );
}

#[test]
fn test_hash_map_completed_rewrite_through_wrappers() {
    let rewritten = rewrite_expr(&make_completed(wrapped_receiver(hash_map_into_iter_var(
        "it",
    ))));
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
        if matches!(inner.as_ref(), PureExpr::Final(inner)
            if matches!(inner.as_ref(), PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Old(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "it"))))));
}

#[test]
fn test_hash_set_iter_now_rewritten() {
    let rewritten = rewrite_expr(&make_produces(
        datatype_var("it", "std::collections::hash_set::Iter"),
        seq_var("visited"),
        datatype_var("next", "std::collections::hash_set::Iter"),
    ));
    // HashSet iterators are now handled — should produce 5-clause FSet partition
    assert_eq!(
        flattened_and_clauses(&rewritten).len(),
        5,
        "HashSet::Iter should now rewrite to a five-clause partition formula"
    );
}

#[test]
fn test_logical_fmap_iter_produces_passthrough() {
    let original = make_produces(
        datatype_var("it", "logic::fmap::Iter"),
        seq_var("visited"),
        datatype_var("next", "logic::fmap::Iter"),
    );
    let rewritten = rewrite_expr(&original);
    assert_eq!(
        rewritten, original,
        "logical FMapIter produces should stay as produces(...) for encoder-side decomposition"
    );
}

#[test]
fn test_logical_fmap_iter_all_sort_aliases() {
    for sort_name in [
        "trust_wp_std::logic::fmap::FMapIter",
        "creusot_std::logic::fmap::Iter",
        "logic::fmap::Iter",
    ] {
        let original = make_produces(
            datatype_var("it", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        );
        let rewritten = rewrite_expr(&original);
        assert_eq!(
            rewritten, original,
            "{sort_name} should bypass driver produces rewrite"
        );
    }
}
