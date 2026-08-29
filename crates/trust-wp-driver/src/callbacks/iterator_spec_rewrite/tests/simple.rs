// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::{
    cloned_var, copied_var, datatype_var, empty_var, filter_map_var, filter_var,
    flattened_and_clauses, fuse_var, make_completed, make_produces, map_inv_var, map_var, once_var,
    repeat_var, rewrite_expr, seq_var, slice_iter_mut_var, slice_iter_var, wrapped_receiver,
};

fn assert_once_initial_branch(branch: &PureExpr) {
    let PureExpr::BinOp(lhs, BinOp::And, rhs) = branch else {
        panic!("expected initial once branch, got {branch:?}");
    };
    assert!(
        matches!(lhs.as_ref(), PureExpr::BinOp(len_lhs, BinOp::Eq, len_rhs)
            if matches!(len_rhs.as_ref(), PureExpr::Int(0))
            && matches!(len_lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")))
    );
    assert!(
        matches!(rhs.as_ref(), PureExpr::BinOp(eq_lhs, BinOp::Eq, eq_rhs)
            if matches!(eq_lhs.as_ref(), PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "o"))
            && matches!(eq_rhs.as_ref(), PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "next")))
    );
}

fn assert_once_exhausted_branch(branch: &PureExpr) {
    let PureExpr::BinOp(lhs, BinOp::And, rhs) = branch else {
        panic!("expected exhausted once branch, got {branch:?}");
    };
    assert!(
        matches!(lhs.as_ref(), PureExpr::BinOp(ne_lhs, BinOp::Ne, ne_rhs)
            if matches!(ne_lhs.as_ref(), PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "o"))
            && matches!(ne_rhs.as_ref(), PureExpr::Var(name, _) if name == "None"))
    );
    assert!(
        matches!(rhs.as_ref(), PureExpr::BinOp(inner_lhs, BinOp::And, inner_rhs)
            if matches!(inner_lhs.as_ref(), PureExpr::BinOp(len_lhs, BinOp::Eq, len_rhs)
                if matches!(len_rhs.as_ref(), PureExpr::Int(1))
                && matches!(len_lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                    if method == "len"
                    && args.is_empty()
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")))
            && matches!(inner_rhs.as_ref(), PureExpr::BinOp(eq_lhs, BinOp::Eq, eq_rhs)
                if matches!(eq_lhs.as_ref(), PureExpr::View(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "next"))
                && matches!(eq_rhs.as_ref(), PureExpr::Var(name, _) if name == "None")))
    );
}

fn assert_repeat_forall(rhs: &PureExpr) {
    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = rhs
    else {
        panic!("expected Forall, got {rhs:?}");
    };
    assert_eq!(var, "__repeat_i");
    assert_eq!(*var_sort, Some(ExprSort::Int));
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 1);
    assert!(
        matches!(&triggers[0][0], PureExpr::MethodCall { method, receiver, args }
        if method == "index_logic"
        && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
        && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__repeat_i"))
    );
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(bounds, BinOp::Implies, eq)
        if matches!(bounds.as_ref(), PureExpr::BinOp(lower, BinOp::And, upper)
            if matches!(lower.as_ref(), PureExpr::BinOp(lhs, BinOp::Le, rhs)
                if matches!(lhs.as_ref(), PureExpr::Int(0))
                && matches!(rhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "__repeat_i"))
            && matches!(upper.as_ref(), PureExpr::BinOp(lhs, BinOp::Lt, rhs)
                if matches!(lhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "__repeat_i")
                && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                    if method == "len"
                    && args.is_empty()
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited"))))
        && matches!(eq.as_ref(), PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "index_logic"
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
                && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__repeat_i"))
            && matches!(rhs.as_ref(), PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "r"))))
    );
}

fn assert_iter_accessor(expr: &PureExpr, receiver_name: &str) {
    assert!(
        matches!(expr, PureExpr::MethodCall { method, receiver, args }
            if method == "iter"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == receiver_name))
    );
}

fn assert_delegated_completed(rewritten: &PureExpr, receiver_name: &str) {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = rewritten
    else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "completed");
    assert!(args.is_empty());
    assert_iter_accessor(receiver.as_ref(), receiver_name);
}

fn assert_delegated_produces(rewritten: &PureExpr, receiver_name: &str, next_name: &str) {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = rewritten
    else {
        panic!("expected MethodCall, got {rewritten:?}");
    };
    assert_eq!(method, "produces");
    assert_eq!(args.len(), 2);
    assert_iter_accessor(receiver.as_ref(), receiver_name);
    assert!(matches!(&args[0], PureExpr::Var(name, _) if name == "visited"));
    assert_iter_accessor(&args[1], next_name);
}

fn assert_deref_adapter_exists(
    rewritten: &PureExpr,
    receiver_name: &str,
    next_name: &str,
    steps_name: &str,
    index_name: &str,
) {
    let PureExpr::Exists {
        var,
        var_sort,
        body,
        triggers,
    } = rewritten
    else {
        panic!("expected Exists, got {rewritten:?}");
    };
    assert_eq!(var, steps_name);
    assert_eq!(*var_sort, Some(ExprSort::Seq));
    assert!(triggers.is_empty());

    let clauses = flattened_and_clauses(body.as_ref());
    let [delegated, len_eq, quantified] = clauses.as_slice() else {
        panic!("expected three clauses, got {clauses:?}");
    };

    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = delegated
    else {
        panic!("expected delegated produces call, got {delegated:?}");
    };
    assert_eq!(method, "produces");
    assert_eq!(args.len(), 2);
    assert_iter_accessor(receiver.as_ref(), receiver_name);
    assert!(matches!(&args[0], PureExpr::Var(name, Some(ExprSort::Seq)) if name == steps_name));
    assert_iter_accessor(&args[1], next_name);

    assert!(matches!(len_eq, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == steps_name))));

    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = quantified
    else {
        panic!("expected forall clause, got {quantified:?}");
    };
    assert_eq!(var, index_name);
    assert_eq!(*var_sort, Some(ExprSort::Int));
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 2);
    assert!(
        matches!(&triggers[0][0], PureExpr::MethodCall { method, receiver, args }
            if method == "index_logic"
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == index_name))
    );
    assert!(
        matches!(&triggers[0][1], PureExpr::MethodCall { method, receiver, args }
            if method == "index_logic"
            && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == steps_name)
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == index_name))
    );
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(bounds, BinOp::Implies, eq)
            if matches!(bounds.as_ref(), PureExpr::BinOp(lower, BinOp::And, upper)
                if matches!(lower.as_ref(), PureExpr::BinOp(lhs, BinOp::Le, rhs)
                    if matches!(lhs.as_ref(), PureExpr::Int(0))
                    && matches!(rhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == index_name))
                && matches!(upper.as_ref(), PureExpr::BinOp(lhs, BinOp::Lt, rhs)
                    if matches!(lhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == index_name)
                    && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                        if method == "len"
                        && args.is_empty()
                        && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == steps_name))))
            && matches!(eq.as_ref(), PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                    if method == "index_logic"
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
                    && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == index_name))
                && matches!(rhs.as_ref(), PureExpr::Deref(inner)
                    if matches!(inner.as_ref(), PureExpr::MethodCall { method, receiver, args }
                        if method == "index_logic"
                        && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == steps_name)
                        && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == index_name)))))
    );
}

#[test]
fn test_empty_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        empty_var("e"),
        seq_var("visited"),
        empty_var("next"),
    ));
    let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::Eq);
    assert!(matches!(rhs.as_ref(), PureExpr::Int(0)));
    assert!(matches!(lhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "len"));
}

#[test]
fn test_empty_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Empty", "std::iter::Empty"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("e", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
            panic!("expected BinOp, got {rewritten:?}");
        };
        assert_eq!(*op, BinOp::Eq);
        assert!(matches!(rhs.as_ref(), PureExpr::Int(0)));
        assert!(matches!(lhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "len"));
    }
}

#[test]
fn test_empty_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(empty_var("e")));
    assert_eq!(rewritten, PureExpr::Bool(true));
}

#[test]
fn test_once_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        once_var("o"),
        seq_var("visited"),
        once_var("next"),
    ));
    let PureExpr::BinOp(branch1, op, branch2) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::Or);
    assert_once_initial_branch(branch1);
    assert_once_exhausted_branch(branch2);
}

#[test]
fn test_once_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Once", "std::iter::Once"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("o", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        let PureExpr::BinOp(branch1, op, branch2) = &rewritten else {
            panic!("expected BinOp, got {rewritten:?}");
        };
        assert_eq!(*op, BinOp::Or);
        assert_once_initial_branch(branch1);
        assert_once_exhausted_branch(branch2);
    }
}

#[test]
fn test_once_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(once_var("o")));
    let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::Eq);
    assert!(matches!(lhs.as_ref(), PureExpr::View(_)));
    assert!(matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == "None"));
}

#[test]
fn test_once_completed_rewrite_through_old_final_view() {
    let rewritten = rewrite_expr(&make_completed(wrapped_receiver(once_var("o"))));
    let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::Eq);
    assert!(matches!(lhs.as_ref(), PureExpr::View(inner)
            if matches!(inner.as_ref(), PureExpr::Final(inner)
                if matches!(inner.as_ref(), PureExpr::View(inner)
                    if matches!(inner.as_ref(), PureExpr::Old(inner)
                        if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "o"))))));
    assert!(matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == "None"));
}

#[test]
fn test_repeat_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        repeat_var("r"),
        seq_var("visited"),
        repeat_var("next"),
    ));
    let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::And);
    let PureExpr::BinOp(eq_lhs, eq_op, eq_rhs) = lhs.as_ref() else {
        panic!("expected inner Eq, got {lhs:?}");
    };
    assert_eq!(*eq_op, BinOp::Eq);
    assert!(matches!(eq_lhs.as_ref(), PureExpr::View(inner)
        if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "r")));
    assert!(matches!(eq_rhs.as_ref(), PureExpr::View(inner)
        if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "next")));
    assert_repeat_forall(rhs.as_ref());
}

#[test]
fn test_repeat_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Repeat", "std::iter::Repeat"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("r", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
            panic!("expected BinOp, got {rewritten:?}");
        };
        assert_eq!(*op, BinOp::And);
        let PureExpr::BinOp(_, eq_op, _) = lhs.as_ref() else {
            panic!("expected inner Eq, got {lhs:?}");
        };
        assert_eq!(*eq_op, BinOp::Eq);
        assert_repeat_forall(rhs.as_ref());
    }
}

#[test]
fn test_repeat_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(repeat_var("r")));
    assert_eq!(rewritten, PureExpr::Bool(false));
}

#[test]
fn test_repeat_produces_has_trigger() {
    let rewritten = rewrite_expr(&make_produces(
        repeat_var("r"),
        seq_var("visited"),
        repeat_var("next"),
    ));
    let PureExpr::BinOp(_, _, rhs) = &rewritten else {
        unreachable!()
    };
    let PureExpr::Forall { triggers, .. } = rhs.as_ref() else {
        panic!("expected Forall, got {rhs:?}");
    };
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 1);
    assert!(
        matches!(&triggers[0][0], PureExpr::MethodCall { method, .. } if method == "index_logic")
    );
}

#[test]
fn test_fuse_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        fuse_var("f"),
        seq_var("visited"),
        fuse_var("next"),
    ));
    assert_delegated_produces(&rewritten, "f", "next");
}

#[test]
fn test_fuse_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Fuse", "std::iter::Fuse"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("f", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        assert_delegated_produces(&rewritten, "f", "next");
    }
}

#[test]
fn test_fuse_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(fuse_var("f")));
    assert_delegated_completed(&rewritten, "f");
}

#[test]
fn test_cloned_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        cloned_var("c"),
        seq_var("visited"),
        cloned_var("next"),
    ));
    assert_deref_adapter_exists(&rewritten, "c", "next", "__cloned_steps", "__cloned_i");
}

#[test]
fn test_cloned_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Cloned", "std::iter::Cloned"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("c", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        assert_deref_adapter_exists(&rewritten, "c", "next", "__cloned_steps", "__cloned_i");
    }
}

#[test]
fn test_cloned_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(cloned_var("c")));
    assert_delegated_completed(&rewritten, "c");
}

#[test]
fn test_copied_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        copied_var("c"),
        seq_var("visited"),
        copied_var("next"),
    ));
    assert_deref_adapter_exists(&rewritten, "c", "next", "__copied_steps", "__copied_i");
}

#[test]
fn test_copied_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Copied", "std::iter::Copied"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("c", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        assert_deref_adapter_exists(&rewritten, "c", "next", "__copied_steps", "__copied_i");
    }
}

#[test]
fn test_copied_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(copied_var("c")));
    assert_delegated_completed(&rewritten, "c");
}

// -- slice::Iter (&Seq<T>) stays fail-closed (#2116) --

#[test]
fn test_slice_iter_produces_stays_unreduced() {
    let original = make_produces(
        slice_iter_var("it"),
        seq_var("visited"),
        slice_iter_var("next"),
    );
    let rewritten = rewrite_expr(&original);
    assert_eq!(rewritten, original);
}

#[test]
fn test_slice_iter_alias_sorts_stay_unreduced() {
    for sort_name in ["core::slice::Iter", "std::slice::Iter"] {
        let original = make_produces(
            datatype_var("it", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        );
        let rewritten = rewrite_expr(&original);
        assert_eq!(rewritten, original, "{sort_name} should stay unchanged");
    }
}

#[test]
fn test_slice_iter_completed_stays_unreduced() {
    let original = make_completed(slice_iter_var("it"));
    let rewritten = rewrite_expr(&original);
    assert_eq!(rewritten, original);
}

// -- slice::IterMut snapshot-aware produces (#2238) --

#[test]
#[allow(clippy::similar_names)] // eq_lhs/eq_rhs and eq_lhs_j/eq_rhs_j are domain-distinct
fn test_slice_iter_mut_produces_rewrite_three_clauses() {
    let rewritten = rewrite_expr(&make_produces(
        slice_iter_mut_var("it"),
        seq_var("visited"),
        slice_iter_mut_var("next"),
    ));
    let clauses = flattened_and_clauses(&rewritten);
    assert_eq!(
        clauses.len(),
        3,
        "expected 3 clauses (len partition, visited snapshot, remainder), got {clauses:?}"
    );

    // Clause 1: length partition — it@.len() == visited.len() + next@.len()
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = clauses[0] else {
        panic!("expected Eq for length partition, got {:?}", clauses[0]);
    };
    assert!(matches!(lhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "len"));
    assert!(matches!(rhs.as_ref(), PureExpr::BinOp(_, BinOp::Add, _)));

    // Clause 2: visited snapshot forall with Deref
    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = clauses[1]
    else {
        panic!("expected Forall for visited snapshot, got {:?}", clauses[1]);
    };
    assert_eq!(var, "__iter_mut_i");
    assert_eq!(*var_sort, Some(ExprSort::Int));
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 2);
    // Body: 0 <= i && i < visited.len() ==> *visited[i] == it@[i]
    let PureExpr::BinOp(_, BinOp::Implies, consequent) = body.as_ref() else {
        panic!("expected Implies in forall body, got {body:?}");
    };
    // The consequent has Deref on the left: *visited.index_logic(i) == it@.index_logic(i)
    let PureExpr::BinOp(eq_lhs, BinOp::Eq, _) = consequent.as_ref() else {
        panic!("expected Eq in consequent, got {consequent:?}");
    };
    assert!(
        matches!(eq_lhs.as_ref(), PureExpr::Deref(_)),
        "visited[i] should be wrapped in Deref for snapshot-aware model"
    );

    // Clause 3: remainder forall without Deref
    let PureExpr::Forall {
        var: var_j,
        var_sort: var_sort_j,
        body: body_j,
        triggers: triggers_j,
    } = clauses[2]
    else {
        panic!("expected Forall for remainder, got {:?}", clauses[2]);
    };
    assert_eq!(var_j, "__iter_mut_j");
    assert_eq!(*var_sort_j, Some(ExprSort::Int));
    assert_eq!(triggers_j.len(), 1);
    assert_eq!(triggers_j[0].len(), 2);
    // Body: 0 <= j && j < next@.len() ==> next@[j] == it@[visited.len() + j]
    let PureExpr::BinOp(_, BinOp::Implies, consequent_j) = body_j.as_ref() else {
        panic!("expected Implies in remainder body, got {body_j:?}");
    };
    let PureExpr::BinOp(eq_lhs_j, BinOp::Eq, eq_rhs_j) = consequent_j.as_ref() else {
        panic!("expected Eq in remainder consequent, got {consequent_j:?}");
    };
    // LHS: next@[j] — no Deref (next is a view, not mutable refs)
    assert!(
        matches!(eq_lhs_j.as_ref(), PureExpr::MethodCall { method, .. } if method == "index_logic"),
        "remainder LHS should be a plain index_logic call, not Deref-wrapped"
    );
    // RHS: it@[visited.len() + j] — has offset addition
    assert!(
        matches!(eq_rhs_j.as_ref(), PureExpr::MethodCall { method, args, .. }
            if method == "index_logic"
            && args.len() == 1
            && matches!(&args[0], PureExpr::BinOp(_, BinOp::Add, _))),
        "remainder RHS should index with offset (visited.len() + j)"
    );
}

#[test]
fn test_slice_iter_mut_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(slice_iter_mut_var("it")));
    let PureExpr::BinOp(lhs, op, rhs) = &rewritten else {
        panic!("expected BinOp, got {rewritten:?}");
    };
    assert_eq!(*op, BinOp::Eq);
    assert!(matches!(rhs.as_ref(), PureExpr::Int(0)));
    // LHS should be len(View(it))
    assert!(
        matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
            if method == "len"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "it")))
    );
}

#[test]
fn test_slice_iter_mut_alias_sorts_rewrite() {
    for sort_name in ["core::slice::IterMut", "std::slice::IterMut"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("it", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        let clauses = flattened_and_clauses(&rewritten);
        assert_eq!(
            clauses.len(),
            3,
            "{sort_name} should produce 3-clause formula"
        );
    }
}

#[test]
fn test_slice_iter_mut_produces_wrong_arity_returns_none() {
    // produces with 0 args (should be 2)
    let original = PureExpr::MethodCall {
        receiver: std::sync::Arc::new(slice_iter_mut_var("it")),
        method: "produces".to_string(),
        args: vec![],
    };
    let rewritten = rewrite_expr(&original);
    // With wrong arity, the dispatch returns None so it falls through to
    // descend_children which just clones the MethodCall
    assert!(matches!(&rewritten, PureExpr::MethodCall { method, .. } if method == "produces"));
}

#[test]
fn test_slice_iter_mut_unknown_method_stays_unreduced() {
    let original = PureExpr::MethodCall {
        receiver: std::sync::Arc::new(slice_iter_mut_var("it")),
        method: "unknown_method".to_string(),
        args: vec![],
    };
    let rewritten = rewrite_expr(&original);
    assert!(
        matches!(&rewritten, PureExpr::MethodCall { method, .. } if method == "unknown_method")
    );
}

// -- Map<I, F> completed delegation (#2170) --

#[test]
fn test_map_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(map_var("m")));
    assert_delegated_completed(&rewritten, "m");
}

#[test]
fn test_map_completed_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Map", "std::iter::Map"] {
        let rewritten = rewrite_expr(&make_completed(datatype_var("m", sort_name)));
        assert_delegated_completed(&rewritten, "m");
    }
}

#[test]
fn test_map_produces_stays_unreduced() {
    let original = make_produces(map_var("m"), seq_var("visited"), map_var("next"));
    let rewritten = rewrite_expr(&original);
    // Produces falls through — should be unchanged (MethodCall with produces)
    assert!(matches!(&rewritten, PureExpr::MethodCall { method, .. } if method == "produces"));
}

// -- Filter<I, P> completed delegation (#2170) --

#[test]
fn test_filter_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(filter_var("f")));
    assert_delegated_completed(&rewritten, "f");
}

#[test]
fn test_filter_completed_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Filter", "std::iter::Filter"] {
        let rewritten = rewrite_expr(&make_completed(datatype_var("f", sort_name)));
        assert_delegated_completed(&rewritten, "f");
    }
}

#[test]
fn test_filter_produces_stays_unreduced() {
    let original = make_produces(filter_var("f"), seq_var("visited"), filter_var("next"));
    let rewritten = rewrite_expr(&original);
    assert!(matches!(&rewritten, PureExpr::MethodCall { method, .. } if method == "produces"));
}

// -- FilterMap<I, F> completed delegation (#2170) --

#[test]
fn test_filter_map_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(filter_map_var("fm")));
    assert_delegated_completed(&rewritten, "fm");
}

#[test]
fn test_filter_map_completed_alias_sorts_rewrite() {
    for sort_name in ["core::iter::FilterMap", "std::iter::FilterMap"] {
        let rewritten = rewrite_expr(&make_completed(datatype_var("fm", sort_name)));
        assert_delegated_completed(&rewritten, "fm");
    }
}

#[test]
fn test_filter_map_produces_stays_unreduced() {
    let original = make_produces(
        filter_map_var("fm"),
        seq_var("visited"),
        filter_map_var("next"),
    );
    let rewritten = rewrite_expr(&original);
    assert!(matches!(&rewritten, PureExpr::MethodCall { method, .. } if method == "produces"));
}

// -- MapInv<I, F> completed delegation (#2170) --

#[test]
fn test_map_inv_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(map_inv_var("mi")));
    assert_delegated_completed(&rewritten, "mi");
}

#[test]
fn test_map_inv_produces_stays_unreduced() {
    let original = make_produces(map_inv_var("mi"), seq_var("visited"), map_inv_var("next"));
    let rewritten = rewrite_expr(&original);
    assert!(matches!(&rewritten, PureExpr::MethodCall { method, .. } if method == "produces"));
}
