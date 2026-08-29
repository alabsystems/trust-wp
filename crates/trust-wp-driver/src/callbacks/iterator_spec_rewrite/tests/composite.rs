// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_core::formula::{
    intern_sort_name, internal::tuple_lowering::tuple_logic_fn_name, BinOp, ExprSort, PureExpr,
};

use super::{
    chain_var, datatype_var, enumerate_var, flattened_and_clauses, make_completed, make_produces,
    peekable_var, rev_var, rewrite_expr, seq_var, skip_var, take_var, zip_var,
};

fn take_mut_ref_var(name: &str, sort_name: &str) -> PureExpr {
    let id = intern_sort_name(sort_name);
    PureExpr::Var(
        name.to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(id)))),
    )
}

fn assert_take_n_call(expr: &PureExpr, receiver_name: &str) {
    assert!(
        matches!(expr, PureExpr::MethodCall { method, receiver, args }
            if method == "n"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == receiver_name))
    );
}

fn assert_take_iter_call(expr: &PureExpr, receiver_name: &str) {
    assert!(
        matches!(expr, PureExpr::MethodCall { method, receiver, args }
            if method == "iter"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == receiver_name))
    );
}

fn assert_skip_iter_call(expr: &PureExpr, receiver_name: &str) {
    assert!(
        matches!(expr, PureExpr::MethodCall { method, receiver, args }
            if method == "iter"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == receiver_name))
    );
}

fn assert_enumerate_iter_call(expr: &PureExpr, receiver_name: &str) {
    assert!(
        matches!(expr, PureExpr::MethodCall { method, receiver, args }
            if method == "iter"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == receiver_name))
    );
}

fn assert_take_produces_len_clause(clause: &PureExpr) {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = clause else {
        panic!("expected Take length equality, got {clause:?}");
    };
    assert_take_n_call(lhs.as_ref(), "t");
    assert!(
        matches!(rhs.as_ref(), PureExpr::BinOp(add_lhs, BinOp::Add, add_rhs)
            if matches!(add_lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next"))
            && matches!(add_rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited"))),
    );
}

fn assert_take_produces_delegation(clause: &PureExpr) {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = clause
    else {
        panic!("expected delegated produces call, got {clause:?}");
    };
    assert_eq!(method, "produces");
    assert_eq!(args.len(), 2);
    assert_take_iter_call(receiver.as_ref(), "t");
    assert!(matches!(&args[0], PureExpr::Var(name, _) if name == "visited"));
    assert_take_iter_call(&args[1], "next");
}

fn assert_take_zero_branch(branch: &PureExpr) {
    let PureExpr::BinOp(lhs, BinOp::And, rhs) = branch else {
        panic!("expected zero-counter branch, got {branch:?}");
    };
    assert!(
        matches!(lhs.as_ref(), PureExpr::BinOp(eq_lhs, BinOp::Eq, eq_rhs)
            if matches!(eq_rhs.as_ref(), PureExpr::Int(0))
            && matches!(eq_lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "t")))
    );
    assert!(matches!(rhs.as_ref(), PureExpr::LogicFnCall { name, args }
            if name == "resolve"
            && matches!(args.as_slice(), [PureExpr::Var(name, _)] if name == "t")));
}

fn assert_take_stepdown_branch(branch: &PureExpr) {
    let clauses = flattened_and_clauses(branch);
    let [gt_clause, eq_clause, delegated_clause] = clauses.as_slice() else {
        panic!("expected three Take completion clauses, got {clauses:?}");
    };

    assert!(matches!(gt_clause, PureExpr::BinOp(lhs, BinOp::Gt, rhs)
            if matches!(rhs.as_ref(), PureExpr::Int(0))
            && matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "t"))));
    assert!(matches!(eq_clause, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "t"))
            && matches!(rhs.as_ref(), PureExpr::BinOp(add_lhs, BinOp::Add, add_rhs)
                if matches!(add_lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                    if method == "n"
                    && args.is_empty()
                    && matches!(receiver.as_ref(), PureExpr::Final(inner)
                        if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "t")))
                && matches!(add_rhs.as_ref(), PureExpr::Int(1)))));
    assert!(
        matches!(delegated_clause, PureExpr::MethodCall { method, receiver, args }
            if method == "completed"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iter_mut"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "t")))
    );
}

fn assert_skip_resolve_prefix(clause: &PureExpr, prefix_name: &str) {
    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = clause
    else {
        panic!("expected Skip resolve quantifier, got {clause:?}");
    };
    assert_eq!(var, "__skip_i");
    assert_eq!(*var_sort, Some(ExprSort::Int));
    assert_eq!(triggers.len(), 1);
    assert!(
        matches!(triggers[0].as_slice(), [PureExpr::MethodCall { method, receiver, args }]
            if method == "index_logic"
            && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == prefix_name)
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__skip_i"))
    );
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(lhs, BinOp::Implies, rhs)
            if matches!(lhs.as_ref(), PureExpr::BinOp(left, BinOp::And, right)
                if matches!(left.as_ref(), PureExpr::BinOp(lhs, BinOp::Le, rhs)
                    if matches!(lhs.as_ref(), PureExpr::Int(0))
                    && matches!(rhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "__skip_i"))
                && matches!(right.as_ref(), PureExpr::BinOp(lhs, BinOp::Lt, rhs)
                    if matches!(lhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "__skip_i")
                    && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                        if method == "len"
                        && args.is_empty()
                        && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == prefix_name))))
            && matches!(rhs.as_ref(), PureExpr::LogicFnCall { name, args }
                if name == "resolve"
                && matches!(args.as_slice(), [PureExpr::MethodCall { method, receiver, args }]
                    if method == "index_logic"
                    && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == prefix_name)
                    && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__skip_i"))))
    );
}

fn assert_skip_empty_branch(branch: &PureExpr) {
    let clauses = flattened_and_clauses(branch);
    let [len_clause, eq_clause] = clauses.as_slice() else {
        panic!("expected two Skip empty-branch clauses, got {clauses:?}");
    };

    assert!(matches!(len_clause, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(rhs.as_ref(), PureExpr::Int(0))
            && matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited"))));
    assert!(matches!(eq_clause, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "s")
            && matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == "next")));
}

fn assert_skip_progress_branch(branch: &PureExpr) {
    let clauses = flattened_and_clauses(branch);
    let [counter_clause, nonempty_clause, exists_clause] = clauses.as_slice() else {
        panic!("expected three Skip progress clauses, got {clauses:?}");
    };

    assert!(
        matches!(counter_clause, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(rhs.as_ref(), PureExpr::Int(0))
            && matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next")))
    );
    assert!(
        matches!(nonempty_clause, PureExpr::BinOp(lhs, BinOp::Gt, rhs)
            if matches!(rhs.as_ref(), PureExpr::Int(0))
            && matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")))
    );

    let PureExpr::Exists {
        var,
        var_sort,
        body,
        triggers,
    } = exists_clause
    else {
        panic!("expected Skip prefix Exists, got {exists_clause:?}");
    };
    assert_eq!(var, "__skip_prefix");
    assert_eq!(*var_sort, Some(ExprSort::Seq));
    assert!(triggers.is_empty());

    let clauses = flattened_and_clauses(body.as_ref());
    let [len_clause, produces_clause, resolve_clause] = clauses.as_slice() else {
        panic!("expected three Skip prefix clauses, got {clauses:?}");
    };

    assert!(matches!(len_clause, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__skip_prefix"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "s"))));
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = produces_clause
    else {
        panic!("expected delegated Skip produces call, got {produces_clause:?}");
    };
    assert_eq!(method, "produces");
    assert_eq!(args.len(), 2);
    assert_skip_iter_call(receiver.as_ref(), "s");
    assert!(
        matches!(&args[0], PureExpr::MethodCall { method, receiver, args: concat_args }
            if method == "concat"
            && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__skip_prefix")
            && matches!(concat_args.as_slice(), [PureExpr::Var(name, _)] if name == "visited"))
    );
    assert_skip_iter_call(&args[1], "next");
    assert_skip_resolve_prefix(resolve_clause, "__skip_prefix");
}

fn assert_skip_completed_exists(exists_clause: &PureExpr) {
    let PureExpr::Exists {
        var,
        var_sort,
        body,
        triggers,
    } = exists_clause
    else {
        panic!("expected outer Skip prefix Exists, got {exists_clause:?}");
    };
    assert_eq!(var, "__skip_prefix");
    assert_eq!(*var_sort, Some(ExprSort::Seq));
    assert!(triggers.is_empty());

    let PureExpr::Exists {
        var,
        body,
        triggers,
        ..
    } = body.as_ref()
    else {
        panic!("expected inner Skip iterator witness Exists, got {body:?}");
    };
    assert_eq!(var, "__skip_done");
    assert!(triggers.is_empty());

    let clauses = flattened_and_clauses(body.as_ref());
    let [len_clause, produces_clause, resolve_clause, completed_clause, final_eq] =
        clauses.as_slice()
    else {
        panic!("expected five Skip completion witness clauses, got {clauses:?}");
    };

    assert!(matches!(len_clause, PureExpr::BinOp(lhs, BinOp::Le, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__skip_prefix"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "s"))));
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = produces_clause
    else {
        panic!("expected delegated Skip completion produces call, got {produces_clause:?}");
    };
    assert_eq!(method, "produces");
    assert_eq!(args.len(), 2);
    assert_skip_iter_call(receiver.as_ref(), "s");
    assert!(
        matches!(&args[0], PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__skip_prefix")
    );
    assert!(matches!(&args[1], PureExpr::Deref(inner)
            if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "__skip_done")));
    assert_skip_resolve_prefix(resolve_clause, "__skip_prefix");
    assert!(
        matches!(completed_clause, PureExpr::MethodCall { method, receiver, args }
            if method == "completed"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "__skip_done"))
    );
    assert!(matches!(final_eq, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::Final(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "__skip_done"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iter"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "s")))));
}

fn assert_enumerate_counter_clause(clause: &PureExpr) {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = clause else {
        panic!("expected Enumerate counter equality, got {clause:?}");
    };
    assert!(
        matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
            if method == "len"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited"))
    );
    assert!(
        matches!(rhs.as_ref(), PureExpr::BinOp(sub_lhs, BinOp::Sub, sub_rhs)
            if matches!(sub_lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next"))
            && matches!(sub_rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "e")))
    );
}

fn assert_enumerate_exists(rewritten: &PureExpr) {
    let PureExpr::Exists {
        var,
        var_sort,
        body,
        triggers,
    } = rewritten
    else {
        panic!("expected Enumerate Exists, got {rewritten:?}");
    };
    assert_eq!(var, "__enumerate_steps");
    assert_eq!(*var_sort, Some(ExprSort::Seq));
    assert!(triggers.is_empty());

    let clauses = flattened_and_clauses(body.as_ref());
    let [delegated, len_eq, quantified] = clauses.as_slice() else {
        panic!("expected three Enumerate inner clauses, got {clauses:?}");
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
    assert_enumerate_iter_call(receiver.as_ref(), "e");
    assert!(
        matches!(&args[0], PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__enumerate_steps")
    );
    assert_enumerate_iter_call(&args[1], "next");

    assert!(matches!(len_eq, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__enumerate_steps"))));

    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = quantified
    else {
        panic!("expected Enumerate forall, got {quantified:?}");
    };
    assert_eq!(var, "__enumerate_i");
    assert_eq!(*var_sort, Some(ExprSort::Int));
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 2);
    assert!(
        matches!(&triggers[0][0], PureExpr::MethodCall { method, receiver, args }
            if method == "index_logic"
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__enumerate_i"))
    );
    assert!(
        matches!(&triggers[0][1], PureExpr::MethodCall { method, receiver, args }
            if method == "index_logic"
            && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__enumerate_steps")
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__enumerate_i"))
    );
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(bounds, BinOp::Implies, eq)
            if matches!(bounds.as_ref(), PureExpr::BinOp(lower, BinOp::And, upper)
                if matches!(lower.as_ref(), PureExpr::BinOp(lhs, BinOp::Le, rhs)
                    if matches!(lhs.as_ref(), PureExpr::Int(0))
                    && matches!(rhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "__enumerate_i"))
                && matches!(upper.as_ref(), PureExpr::BinOp(lhs, BinOp::Lt, rhs)
                    if matches!(lhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "__enumerate_i")
                    && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                        if method == "len"
                        && args.is_empty()
                        && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__enumerate_steps"))))
            && matches!(eq.as_ref(), PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                    if method == "index_logic"
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
                    && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__enumerate_i"))
                && matches!(rhs.as_ref(), PureExpr::LogicFnCall { name, args }
                    if name == &tuple_logic_fn_name(2)
                    && matches!(args.as_slice(), [first, second]
                        if matches!(first, PureExpr::BinOp(add_lhs, BinOp::Add, add_rhs)
                            if matches!(add_lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                                if method == "n"
                                && args.is_empty()
                                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "e"))
                            && matches!(add_rhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "__enumerate_i"))
                        && matches!(second, PureExpr::MethodCall { method, receiver, args }
                            if method == "index_logic"
                            && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__enumerate_steps")
                            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__enumerate_i"))))))
    );
}

fn assert_zip_produces_exists(rewritten: &PureExpr) {
    let PureExpr::Exists {
        var,
        var_sort,
        body,
        triggers,
    } = rewritten
    else {
        panic!("expected outer Zip Exists, got {rewritten:?}");
    };
    assert_eq!(var, "__zip_left_steps");
    assert_eq!(*var_sort, Some(ExprSort::Seq));
    assert!(triggers.is_empty());

    let PureExpr::Exists {
        var,
        var_sort,
        body,
        triggers,
    } = body.as_ref()
    else {
        panic!("expected inner Zip Exists, got {body:?}");
    };
    assert_eq!(var, "__zip_right_steps");
    assert_eq!(*var_sort, Some(ExprSort::Seq));
    assert!(triggers.is_empty());

    let clauses = flattened_and_clauses(body.as_ref());
    let [len_eq, visited_len_eq, left_produces, right_produces, quantified] = clauses.as_slice()
    else {
        panic!("expected five Zip clauses, got {clauses:?}");
    };

    assert!(matches!(len_eq, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__zip_left_steps"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__zip_right_steps"))));
    assert!(
        matches!(visited_len_eq, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__zip_right_steps"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")))
    );
    assert!(
        matches!(left_produces, PureExpr::MethodCall { method, receiver, args }
            if method == "produces"
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "itera"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "z"))
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Seq)), PureExpr::MethodCall { method, receiver, args: right_args }]
                if name == "__zip_left_steps"
                && method == "itera"
                && right_args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next")))
    );
    assert!(
        matches!(right_produces, PureExpr::MethodCall { method, receiver, args }
            if method == "produces"
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iterb"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "z"))
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Seq)), PureExpr::MethodCall { method, receiver, args: right_args }]
                if name == "__zip_right_steps"
                && method == "iterb"
                && right_args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next")))
    );

    let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = quantified
    else {
        panic!("expected Zip forall, got {quantified:?}");
    };
    assert_eq!(var, "__zip_i");
    assert_eq!(*var_sort, Some(ExprSort::Int));
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 3);
    assert!(
        matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Implies, eq)
            if matches!(eq.as_ref(), PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                    if method == "index_logic"
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "visited")
                    && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__zip_i"))
                && matches!(rhs.as_ref(), PureExpr::LogicFnCall { name, args }
                    if name == &tuple_logic_fn_name(2)
                    && matches!(args.as_slice(), [left, right]
                        if matches!(left, PureExpr::MethodCall { method, receiver, args }
                            if method == "index_logic"
                            && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__zip_left_steps")
                            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__zip_i"))
                        && matches!(right, PureExpr::MethodCall { method, receiver, args }
                            if method == "index_logic"
                            && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__zip_right_steps")
                            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Int))] if name == "__zip_i"))))))
    );
}

fn assert_zip_completed_left_branch(branch: &PureExpr) {
    let clauses = flattened_and_clauses(branch);
    let [completed_clause, left_eq, right_eq] = clauses.as_slice() else {
        panic!("expected three Zip left-branch clauses, got {clauses:?}");
    };

    assert!(
        matches!(completed_clause, PureExpr::MethodCall { method, receiver, args }
            if method == "completed"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "itera"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "z")))
    );
    assert!(matches!(left_eq, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "itera"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "z"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "itera"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "z")))));
    assert!(matches!(right_eq, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iterb"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "z"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iterb"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "z")))));
}

fn assert_zip_completed_right_branch(branch: &PureExpr) {
    let clauses = flattened_and_clauses(branch);
    let [completed_clause, stable_right, exists_clause] = clauses.as_slice() else {
        panic!("expected three Zip right-branch clauses, got {clauses:?}");
    };

    assert!(
        matches!(completed_clause, PureExpr::MethodCall { method, receiver, args }
            if method == "completed"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iterb"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "z")))
    );
    assert!(matches!(stable_right, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iterb"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "z"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iterb"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "z")))));

    let PureExpr::Exists {
        var,
        var_sort,
        body,
        triggers,
    } = exists_clause
    else {
        panic!("expected Zip step witness exists, got {exists_clause:?}");
    };
    assert_eq!(var, "__zip_left_step");
    assert_eq!(*var_sort, Some(ExprSort::Seq));
    assert!(triggers.is_empty());

    let clauses = flattened_and_clauses(body.as_ref());
    let [len_clause, produces_clause, inv_clause, resolve_clause] = clauses.as_slice() else {
        panic!("expected four Zip witness clauses, got {clauses:?}");
    };
    assert!(matches!(len_clause, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__zip_left_step"))
            && matches!(rhs.as_ref(), PureExpr::Int(1))));
    assert!(
        matches!(produces_clause, PureExpr::MethodCall { method, receiver, args }
            if method == "produces"
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "itera"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "z"))
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Seq)), PureExpr::MethodCall { method, receiver, args: right_args }]
                if name == "__zip_left_step"
                && method == "itera"
                && right_args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "z"))))
    );
    assert!(matches!(inv_clause, PureExpr::LogicFnCall { name, args }
            if name == "inv"
            && matches!(args.as_slice(), [PureExpr::MethodCall { method, receiver, args: idx_args }]
                if method == "index_logic"
                && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__zip_left_step")
                && matches!(idx_args.as_slice(), [PureExpr::Int(0)]))));
    assert!(
        matches!(resolve_clause, PureExpr::LogicFnCall { name, args }
            if name == "resolve"
            && matches!(args.as_slice(), [PureExpr::MethodCall { method, receiver, args: idx_args }]
                if method == "index_logic"
                && matches!(receiver.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "__zip_left_step")
                && matches!(idx_args.as_slice(), [PureExpr::Int(0)])))
    );
}

#[test]
fn test_rev_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        rev_var("r"),
        seq_var("visited"),
        rev_var("next"),
    ));
    // Rev::produces delegates to inner.produces_back
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = &rewritten
    else {
        panic!("expected Rev produces delegation, got {rewritten:?}");
    };
    assert_eq!(method, "produces_back");
    assert_eq!(args.len(), 2);
    // receiver is iter(r)
    assert!(
        matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver: inner, args: m_args }
            if method == "iter"
            && m_args.is_empty()
            && matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "r"))
    );
    // first arg is visited (rewritten)
    assert!(matches!(&args[0], PureExpr::Var(name, _) if name == "visited"));
    // second arg is iter(next)
    assert!(
        matches!(&args[1], PureExpr::MethodCall { method, receiver: inner, args: m_args }
            if method == "iter"
            && m_args.is_empty()
            && matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "next"))
    );
}

#[test]
fn test_rev_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Rev", "std::iter::Rev"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("r", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        assert!(
            matches!(rewritten, PureExpr::MethodCall { method, .. } if method == "produces_back"),
            "{sort_name} should rewrite to the Rev produces_back delegation"
        );
    }
}

#[test]
fn test_rev_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(take_mut_ref_var(
        "r",
        "core::iter::adapters::rev::Rev",
    )));
    // Rev::completed delegates to iter(recv).completed()
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = &rewritten
    else {
        panic!("expected Rev completed delegation, got {rewritten:?}");
    };
    assert_eq!(method, "completed");
    assert!(args.is_empty());
    // receiver is iter(rewrite_expr(recv))
    assert!(
        matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver: inner, args: m_args }
            if method == "iter"
            && m_args.is_empty()
            && matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "r"))
    );
}

#[test]
fn test_rev_completed_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Rev", "std::iter::Rev"] {
        let rewritten = rewrite_expr(&make_completed(take_mut_ref_var("r", sort_name)));
        assert!(
            matches!(rewritten, PureExpr::MethodCall { method, .. } if method == "completed"),
            "{sort_name} should rewrite to the Rev completed delegation"
        );
    }
}

#[test]
fn test_skip_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        skip_var("s"),
        seq_var("visited"),
        skip_var("next"),
    ));
    let PureExpr::BinOp(empty_branch, BinOp::Or, progress_branch) = &rewritten else {
        panic!("expected Skip produces disjunction, got {rewritten:?}");
    };

    assert_skip_empty_branch(empty_branch);
    assert_skip_progress_branch(progress_branch);
}

#[test]
fn test_skip_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Skip", "std::iter::Skip"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("s", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        assert!(
            matches!(rewritten, PureExpr::BinOp(_, BinOp::Or, _)),
            "{sort_name} should rewrite to the Skip produces disjunction"
        );
    }
}

#[test]
fn test_skip_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(take_mut_ref_var(
        "s",
        "core::iter::adapters::skip::Skip",
    )));
    let clauses = flattened_and_clauses(&rewritten);
    let [counter_clause, exists_clause] = clauses.as_slice() else {
        panic!("expected two Skip completion clauses, got {clauses:?}");
    };

    assert!(
        matches!(counter_clause, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(rhs.as_ref(), PureExpr::Int(0))
            && matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "s"))))
    );
    assert_skip_completed_exists(exists_clause);
}

#[test]
fn test_skip_completed_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Skip", "std::iter::Skip"] {
        let rewritten = rewrite_expr(&make_completed(take_mut_ref_var("s", sort_name)));
        let clauses = flattened_and_clauses(&rewritten);
        assert_eq!(
            clauses.len(),
            2,
            "{sort_name} should rewrite to the Skip completion conjunction"
        );
        assert!(matches!(clauses[1], PureExpr::Exists { .. }));
    }
}

#[test]
fn test_take_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        take_var("t"),
        seq_var("visited"),
        take_var("next"),
    ));
    let clauses = flattened_and_clauses(&rewritten);
    let [len_clause, delegated_clause] = clauses.as_slice() else {
        panic!("expected two Take produces clauses, got {clauses:?}");
    };

    assert_take_produces_len_clause(len_clause);
    assert_take_produces_delegation(delegated_clause);
}

#[test]
fn test_take_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Take", "std::iter::Take"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("t", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        let clauses = flattened_and_clauses(&rewritten);
        assert_eq!(
            clauses.len(),
            2,
            "{sort_name} should rewrite to the Take two-clause formula"
        );
    }
}

#[test]
fn test_take_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(take_mut_ref_var(
        "t",
        "core::iter::adapters::take::Take",
    )));
    let PureExpr::BinOp(zero_branch, BinOp::Or, step_branch) = &rewritten else {
        panic!("expected Take completion disjunction, got {rewritten:?}");
    };

    assert_take_zero_branch(zero_branch);
    assert_take_stepdown_branch(step_branch);
}

#[test]
fn test_take_completed_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Take", "std::iter::Take"] {
        let rewritten = rewrite_expr(&make_completed(take_mut_ref_var("t", sort_name)));
        assert!(
            matches!(rewritten, PureExpr::BinOp(_, BinOp::Or, _)),
            "{sort_name} should rewrite to the Take completion disjunction"
        );
    }
}

#[test]
fn test_enumerate_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        enumerate_var("e"),
        seq_var("visited"),
        enumerate_var("next"),
    ));
    let clauses = flattened_and_clauses(&rewritten);
    let [counter_clause, exists_clause] = clauses.as_slice() else {
        panic!("expected two Enumerate top-level clauses, got {clauses:?}");
    };

    assert_enumerate_counter_clause(counter_clause);
    assert_enumerate_exists(exists_clause);
}

#[test]
fn test_enumerate_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Enumerate", "std::iter::Enumerate"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("e", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        let clauses = flattened_and_clauses(&rewritten);
        assert_eq!(
            clauses.len(),
            2,
            "{sort_name} should rewrite to the Enumerate two-clause formula"
        );
    }
}

#[test]
fn test_enumerate_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(take_mut_ref_var(
        "e",
        "core::iter::adapters::enumerate::Enumerate",
    )));
    let clauses = flattened_and_clauses(&rewritten);
    let [completed_clause, iter_eq, counter_eq] = clauses.as_slice() else {
        panic!("expected three Enumerate completion clauses, got {clauses:?}");
    };

    assert!(
        matches!(completed_clause, PureExpr::MethodCall { method, receiver, args }
            if method == "completed"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iter"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "e")))
    );
    assert!(matches!(iter_eq, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iter"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "e"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "iter"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "e")))));
    assert!(matches!(counter_eq, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "e"))
            && matches!(rhs.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "n"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "e")))));
}

#[test]
fn test_zip_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        zip_var("z"),
        seq_var("visited"),
        zip_var("next"),
    ));
    assert_zip_produces_exists(&rewritten);
}

#[test]
fn test_zip_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Zip", "std::iter::Zip"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("z", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        assert!(
            matches!(rewritten, PureExpr::Exists { .. }),
            "{sort_name} should rewrite to nested Zip existentials"
        );
    }
}

#[test]
fn test_zip_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(take_mut_ref_var(
        "z",
        "core::iter::adapters::zip::Zip",
    )));
    let PureExpr::BinOp(left_branch, BinOp::Or, right_branch) = &rewritten else {
        panic!("expected Zip completion disjunction, got {rewritten:?}");
    };

    assert_zip_completed_left_branch(left_branch);
    assert_zip_completed_right_branch(right_branch);
}

// ---------------------------------------------------------------------------
// Chain<A, B> — dual-source sequential concatenation (#2688)
// ---------------------------------------------------------------------------

#[test]
fn test_chain_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        chain_var("c"),
        seq_var("visited"),
        chain_var("next"),
    ));

    // Should produce nested Exists for __chain_left and __chain_right
    let PureExpr::Exists {
        var,
        var_sort,
        body,
        triggers,
    } = &rewritten
    else {
        panic!("expected outer Chain Exists, got {rewritten:?}");
    };
    assert_eq!(var, "__chain_left");
    assert_eq!(*var_sort, Some(ExprSort::Seq));
    assert!(triggers.is_empty());

    let PureExpr::Exists {
        var,
        var_sort,
        body,
        triggers,
    } = body.as_ref()
    else {
        panic!("expected inner Chain Exists, got {body:?}");
    };
    assert_eq!(var, "__chain_right");
    assert_eq!(*var_sort, Some(ExprSort::Seq));
    assert!(triggers.is_empty());

    let clauses = flattened_and_clauses(body.as_ref());
    // Should have: left_produces, right_produces, len_constraint,
    //              left_content (Forall), right_content (Forall)
    assert_eq!(
        clauses.len(),
        5,
        "expected five Chain produces clauses, got {clauses:?}"
    );

    // Check left produces delegation: c.a().produces(__chain_left, next.a())
    // Chain uses a()/b() accessors per trust-wp-std ChainExt trait spec
    let left_produces = clauses[0];
    assert!(
        matches!(left_produces, PureExpr::MethodCall { method, receiver, args }
            if method == "produces"
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "a"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "c"))
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Seq)), PureExpr::MethodCall { method, receiver, args: r_args }]
                if name == "__chain_left"
                && method == "a"
                && r_args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next")))
    );

    // Check right produces delegation: c.b().produces(__chain_right, next.b())
    let right_produces = clauses[1];
    assert!(
        matches!(right_produces, PureExpr::MethodCall { method, receiver, args }
            if method == "produces"
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "b"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "c"))
            && matches!(args.as_slice(), [PureExpr::Var(name, Some(ExprSort::Seq)), PureExpr::MethodCall { method, receiver, args: r_args }]
                if name == "__chain_right"
                && method == "b"
                && r_args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "next")))
    );

    // Check length constraint
    let len_constraint = clauses[2];
    assert!(
        matches!(len_constraint, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
        if matches!(lhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "len")
        && matches!(rhs.as_ref(), PureExpr::BinOp(_, BinOp::Add, _)))
    );

    // Check left content forall
    let left_forall = clauses[3];
    assert!(
        matches!(left_forall, PureExpr::Forall { var, var_sort, triggers, .. }
        if var == "__chain_i"
        && *var_sort == Some(ExprSort::Int)
        && triggers.len() == 1
        && triggers[0].len() == 2)
    );

    // Check right content forall
    let right_forall = clauses[4];
    assert!(
        matches!(right_forall, PureExpr::Forall { var, var_sort, triggers, .. }
        if var == "__chain_j"
        && *var_sort == Some(ExprSort::Int)
        && triggers.len() == 1
        && triggers[0].len() == 2)
    );
}

#[test]
fn test_chain_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Chain", "std::iter::Chain"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("c", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        assert!(
            matches!(rewritten, PureExpr::Exists { .. }),
            "{sort_name} should rewrite to nested Chain existentials"
        );
    }
}

#[test]
fn test_chain_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(take_mut_ref_var(
        "c",
        "core::iter::adapters::chain::Chain",
    )));

    // Should produce: c.a().completed() && c.b().completed()
    // Chain uses a()/b() accessors per trust-wp-std ChainExt trait spec
    let clauses = flattened_and_clauses(&rewritten);
    assert_eq!(
        clauses.len(),
        2,
        "expected two Chain completion clauses, got {clauses:?}"
    );

    // Left completed
    assert!(
        matches!(clauses[0], PureExpr::MethodCall { method, receiver, args }
            if method == "completed"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "a"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "c")))
    );

    // Right completed
    assert!(
        matches!(clauses[1], PureExpr::MethodCall { method, receiver, args }
            if method == "completed"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver, args }
                if method == "b"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "c")))
    );
}

#[test]
fn test_chain_completed_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Chain", "std::iter::Chain"] {
        let rewritten = rewrite_expr(&make_completed(take_mut_ref_var("c", sort_name)));
        let clauses = flattened_and_clauses(&rewritten);
        assert_eq!(
            clauses.len(),
            2,
            "{sort_name} should rewrite to the Chain completion conjunction"
        );
    }
}

// ---------------------------------------------------------------------------
// Peekable<I> — look-ahead wrapper (#2688)
// ---------------------------------------------------------------------------

#[test]
fn test_peekable_produces_rewrite() {
    let rewritten = rewrite_expr(&make_produces(
        peekable_var("p"),
        seq_var("visited"),
        peekable_var("next"),
    ));

    // Peekable delegates to inner: p.iter().produces(visited, next.iter())
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = &rewritten
    else {
        panic!("expected Peekable produces delegation, got {rewritten:?}");
    };
    assert_eq!(method, "produces");
    assert_eq!(args.len(), 2);
    // receiver is iter(p)
    assert!(
        matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver: inner, args: m_args }
            if method == "iter"
            && m_args.is_empty()
            && matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "p"))
    );
    // first arg is visited (rewritten)
    assert!(matches!(&args[0], PureExpr::Var(name, _) if name == "visited"));
    // second arg is iter(next)
    assert!(
        matches!(&args[1], PureExpr::MethodCall { method, receiver: inner, args: m_args }
            if method == "iter"
            && m_args.is_empty()
            && matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "next"))
    );
}

#[test]
fn test_peekable_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Peekable", "std::iter::Peekable"] {
        let rewritten = rewrite_expr(&make_produces(
            datatype_var("p", sort_name),
            seq_var("visited"),
            datatype_var("next", sort_name),
        ));
        assert!(
            matches!(rewritten, PureExpr::MethodCall { method, .. } if method == "produces"),
            "{sort_name} should rewrite to the Peekable produces delegation"
        );
    }
}

#[test]
fn test_peekable_completed_rewrite() {
    let rewritten = rewrite_expr(&make_completed(take_mut_ref_var(
        "p",
        "core::iter::adapters::peekable::Peekable",
    )));

    // Peekable delegates: p.iter().completed()
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = &rewritten
    else {
        panic!("expected Peekable completed delegation, got {rewritten:?}");
    };
    assert_eq!(method, "completed");
    assert!(args.is_empty());
    assert!(
        matches!(receiver.as_ref(), PureExpr::MethodCall { method, receiver: inner, args: m_args }
            if method == "iter"
            && m_args.is_empty()
            && matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "p"))
    );
}

#[test]
fn test_peekable_completed_alias_sorts_rewrite() {
    for sort_name in ["core::iter::Peekable", "std::iter::Peekable"] {
        let rewritten = rewrite_expr(&make_completed(take_mut_ref_var("p", sort_name)));
        assert!(
            matches!(rewritten, PureExpr::MethodCall { method, .. } if method == "completed"),
            "{sort_name} should rewrite to the Peekable completed delegation"
        );
    }
}

#[test]
fn test_chain_produces_wrong_arity_returns_none() {
    // produces with wrong number of args should return None (fall through)
    let input = PureExpr::MethodCall {
        receiver: std::sync::Arc::new(chain_var("c")),
        method: "produces".to_string(),
        args: vec![seq_var("visited")], // only 1 arg instead of 2
    };
    let rewritten = rewrite_expr(&input);
    // Should be unchanged (descend_children just clones)
    assert!(
        matches!(rewritten, PureExpr::MethodCall { method, args, .. }
        if method == "produces" && args.len() == 1)
    );
}
