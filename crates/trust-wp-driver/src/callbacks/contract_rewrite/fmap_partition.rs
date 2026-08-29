// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Rewrites the exact FMap `get == Some(v)` partition invariant shape from
//! `ghost/fmap_iter.rs` into an equivalent single-key invariant.

use std::sync::Arc;

use trust_wp_core::formula::{resolve_sort_name, BinOp, ExprSort, PureExpr};

use crate::callbacks::parsing::ParsedContract;

pub(super) fn rewrite_parsed_contract_fmap_partition_get_some_invariants(
    parsed: &mut ParsedContract,
) {
    parsed.rewrite_all_exprs(rewrite_fmap_partition_get_some_expr);
}

pub(super) fn rewrite_fmap_partition_get_some_expr(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(rewrite_fmap_partition_get_some_node)
}

fn rewrite_fmap_partition_get_some_node(node: PureExpr) -> PureExpr {
    let PureExpr::Forall {
        var: key_var,
        var_sort: key_sort,
        body,
        triggers,
    } = &node
    else {
        return node;
    };
    if !triggers.is_empty() {
        return node;
    }

    let PureExpr::Forall {
        var: value_var,
        body: inner_body,
        triggers: inner_triggers,
        ..
    } = body.as_ref()
    else {
        return node;
    };
    if !inner_triggers.is_empty() {
        return node;
    }

    let Some((source, left, right)) = match_partition_equivalence(inner_body, key_var, value_var)
    else {
        return node;
    };

    let key_expr = PureExpr::Var(key_var.clone(), key_sort.clone());
    let source_contains = contains(source.clone(), key_expr.clone());
    let left_contains = contains(left.clone(), key_expr.clone());
    let right_contains = contains(right.clone(), key_expr.clone());
    let source_lookup = lookup(source, key_expr.clone());

    let partition = eq(
        source_contains,
        or(left_contains.clone(), right_contains.clone()),
    );
    let left_value = implies(
        left_contains,
        eq(lookup(left, key_expr.clone()), source_lookup.clone()),
    );
    let right_value = implies(right_contains, eq(lookup(right, key_expr), source_lookup));

    // Emit top-level quantified clauses rather than one quantified conjunction
    // so obligation_slices can isolate the partition/value obligations. (#2116)
    and(
        forall(key_var, key_sort.clone(), partition),
        and(
            forall(key_var, key_sort.clone(), left_value),
            forall(key_var, key_sort.clone(), right_value),
        ),
    )
}

fn match_partition_equivalence(
    expr: &PureExpr,
    key_var: &str,
    value_var: &str,
) -> Option<(PureExpr, PureExpr, PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };

    if let Some(source) = match_get_some_atom(lhs, key_var, value_var) {
        if let Some((left, right)) = match_get_some_disjunction(rhs, key_var, value_var) {
            return Some((source, left, right));
        }
    }
    if let Some(source) = match_get_some_atom(rhs, key_var, value_var) {
        if let Some((left, right)) = match_get_some_disjunction(lhs, key_var, value_var) {
            return Some((source, left, right));
        }
    }

    None
}

fn match_get_some_disjunction(
    expr: &PureExpr,
    key_var: &str,
    value_var: &str,
) -> Option<(PureExpr, PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Or, rhs) = expr else {
        return None;
    };
    let left = match_get_some_atom(lhs, key_var, value_var)?;
    let right = match_get_some_atom(rhs, key_var, value_var)?;
    Some((left, right))
}

fn match_get_some_atom(expr: &PureExpr, key_var: &str, value_var: &str) -> Option<PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };

    if let Some(receiver) = match_get_call(lhs, key_var) {
        if is_some_var(rhs, value_var) {
            return Some(receiver);
        }
    }
    if let Some(receiver) = match_get_call(rhs, key_var) {
        if is_some_var(lhs, value_var) {
            return Some(receiver);
        }
    }

    None
}

fn match_get_call(expr: &PureExpr, key_var: &str) -> Option<PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method != "get" || args.len() != 1 {
        return None;
    }
    if !matches!(&args[0], PureExpr::Var(name, _) if name == key_var) {
        return None;
    }
    if !is_fmap_like_receiver(receiver.as_ref()) {
        return None;
    }
    Some(receiver.as_ref().clone())
}

fn is_some_var(expr: &PureExpr, value_var: &str) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if name == "Some"
                && args.len() == 1
                && matches!(&args[0], PureExpr::Var(name, _) if name == value_var)
    )
}

fn is_fmap_like_receiver(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, Some(ExprSort::FMap)) => true,
        PureExpr::View(inner) => is_fmap_like_view_inner(inner.as_ref()),
        _ => false,
    }
}

fn is_fmap_like_view_inner(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, Some(ExprSort::FMap)) => true,
        PureExpr::Var(_, Some(ExprSort::Datatype(sort_name))) => {
            resolve_sort_name(*sort_name).contains("FMapIter")
        }
        _ => false,
    }
}

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

fn contains(receiver: PureExpr, key: PureExpr) -> PureExpr {
    method_call(receiver, "contains", vec![key])
}

fn lookup(receiver: PureExpr, key: PureExpr) -> PureExpr {
    method_call(receiver, "lookup", vec![key])
}

fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
}

fn and(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs))
}

fn or(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Or, Arc::new(rhs))
}

fn implies(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Implies, Arc::new(rhs))
}

fn forall(var: &str, var_sort: Option<ExprSort>, body: PureExpr) -> PureExpr {
    PureExpr::Forall {
        var: var.to_string(),
        var_sort,
        body: Arc::new(body),
        triggers: vec![],
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

    use super::rewrite_fmap_partition_get_some_expr;

    fn fmap_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::FMap))
    }

    fn fmap_iter_view(name: &str) -> PureExpr {
        PureExpr::View(Arc::new(PureExpr::Var(
            name.to_string(),
            Some(ExprSort::Datatype(intern_sort_name(
                "trust_wp_std::logic::fmap::FMapIter",
            ))),
        )))
    }

    fn key_var() -> PureExpr {
        PureExpr::Var("k".to_string(), None)
    }

    fn val_var() -> PureExpr {
        PureExpr::Var("v".to_string(), None)
    }

    fn flatten_top_level_and<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
        match expr {
            PureExpr::BinOp(lhs, BinOp::And, rhs) => {
                flatten_top_level_and(lhs, out);
                flatten_top_level_and(rhs, out);
            }
            _ => out.push(expr),
        }
    }

    fn get_some(receiver: PureExpr) -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(receiver),
                method: "get".to_string(),
                args: vec![key_var()],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "Some".to_string(),
                args: vec![val_var()],
            }),
        )
    }

    #[test]
    fn rewrites_fmap_partition_get_some_quantifier_to_single_key_form() {
        let expr = PureExpr::Forall {
            var: "k".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::Forall {
                var: "v".to_string(),
                var_sort: Some(ExprSort::Int),
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(get_some(fmap_var("m_snap"))),
                    BinOp::Eq,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(get_some(fmap_var("result"))),
                        BinOp::Or,
                        Arc::new(get_some(fmap_iter_view("iter"))),
                    )),
                )),
                triggers: vec![],
            }),
            triggers: vec![],
        };

        let rewritten = rewrite_fmap_partition_get_some_expr(&expr);
        let mut clauses = Vec::new();
        flatten_top_level_and(&rewritten, &mut clauses);
        assert_eq!(
            clauses.len(),
            3,
            "rewritten partition invariant should expose 3 top-level clauses: {rewritten}"
        );

        let mut partition_clause_count = 0;
        let mut lookup_implication_count = 0;
        for clause in &clauses {
            let PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } = clause
            else {
                panic!("expected quantified clause, got {clause:?}");
            };
            assert_eq!(var, "k");
            assert_eq!(var_sort, &Some(ExprSort::Int));
            assert!(
                triggers.is_empty(),
                "rewritten clauses should stay triggerless for later synthesis"
            );

            let text = format!("{body}");
            assert!(
                !text.contains("Some("),
                "rewritten partition invariant should not retain Some(v) quantification: {text}"
            );
            assert!(
                !text.contains("forall v"),
                "rewritten partition invariant should eliminate the value quantifier: {text}"
            );

            match body.as_ref() {
                PureExpr::BinOp(_, BinOp::Eq, _) => {
                    partition_clause_count += 1;
                    assert!(
                        text.contains("contains"),
                        "partition clause should use contains atoms: {text}"
                    );
                }
                PureExpr::BinOp(_, BinOp::Implies, _) => {
                    lookup_implication_count += 1;
                    assert!(
                        text.contains("lookup"),
                        "value-preservation clause should use lookup atoms: {text}"
                    );
                }
                other => panic!("expected Eq or Implies body, got {other:?}"),
            }
        }

        assert!(
            partition_clause_count == 1,
            "expected one partition clause, got {partition_clause_count} in {clauses:?}"
        );
        assert!(
            lookup_implication_count == 2,
            "expected two lookup-preservation clauses, got {lookup_implication_count} in {clauses:?}"
        );
    }

    #[test]
    fn leaves_non_fmap_receivers_unchanged() {
        let expr = PureExpr::Forall {
            var: "k".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::Forall {
                var: "v".to_string(),
                var_sort: Some(ExprSort::Int),
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(get_some(PureExpr::Var(
                        "seq".to_string(),
                        Some(ExprSort::Seq),
                    ))),
                    BinOp::Eq,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(get_some(PureExpr::Var(
                            "result".to_string(),
                            Some(ExprSort::Seq),
                        ))),
                        BinOp::Or,
                        Arc::new(get_some(PureExpr::Var(
                            "rest".to_string(),
                            Some(ExprSort::Seq),
                        ))),
                    )),
                )),
                triggers: vec![],
            }),
            triggers: vec![],
        };

        assert_eq!(rewrite_fmap_partition_get_some_expr(&expr), expr);
    }

    #[test]
    fn leaves_user_triggered_quantifier_unchanged() {
        let expr = PureExpr::Forall {
            var: "k".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::Forall {
                var: "v".to_string(),
                var_sort: Some(ExprSort::Int),
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(get_some(fmap_var("m_snap"))),
                    BinOp::Eq,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(get_some(fmap_var("result"))),
                        BinOp::Or,
                        Arc::new(get_some(fmap_iter_view("iter"))),
                    )),
                )),
                triggers: vec![vec![PureExpr::MethodCall {
                    receiver: Arc::new(fmap_var("m_snap")),
                    method: "get".to_string(),
                    args: vec![key_var()],
                }]],
            }),
            triggers: vec![],
        };

        assert_eq!(rewrite_fmap_partition_get_some_expr(&expr), expr);
    }
}
