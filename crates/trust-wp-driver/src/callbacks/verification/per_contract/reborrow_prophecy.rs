// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sound prophecy premises for recognized recursive match-reborrow functions.

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

/// Synthesize the prophecy-pinning premise for a recognized recursive
/// `&mut self` match-reborrow function (rusthorn `take_some` and analogues).
///
/// The receiver is matched into a single non-diverging enum variant
/// `Variant(f_0, .., f_{n-1})`, each field is reborrowed, and the returned
/// reference is one field's reborrow (or the result of recursing on a field)
/// selected by data-independent branches. Standard RustHorn prophecy semantics
/// then give the sound structural fact
///
/// ```text
///   ^self == Variant(g_0, .., g_{n-1})
///   where g_i == *self.i   whenever field i is NOT the one returned/recursed
/// ```
///
/// i.e. the constructor is preserved (the body never overwrites `*self` — see
/// the mutation-free gate in `analyze_reborrow_prophecy`), and every field that
/// is *not* borrowed out along a given branch resolves to its current value.
/// We emit this as three provably-sound conjuncts:
///
/// * `discriminant(^self) == D`  (constructor preserved);
/// * for each field `i`: `¬touched_i ⇒ (^self).i == (*self).i`, where
///   `touched_i` is the disjunction of the branch conditions under which field
///   `i`'s reborrow is returned directly or recursed upon.
///
/// The per-branch touched field is read from `result_expr` (direct field leaves
/// `__trust_wp_tuple_get_i(self)`) and from `info.call_local_to_field` (which
/// field each recursion touches via its receiver). The analysis is fail-closed:
/// any unrecognized leaf yields no premise.
pub(super) fn build_reborrow_prophecy_premises(
    result_expr: &PureExpr,
    info: &crate::mir_analysis::ReborrowProphecyInfo,
) -> Vec<PureExpr> {
    // result_expr = LetAssume { assumption: discriminant(*self) == D, body }.
    let PureExpr::LetAssume { assumption, body } = result_expr else {
        return vec![];
    };
    let Some((self_var, disc)) = match_discriminant_eq(assumption) else {
        return vec![];
    };

    // Collect (field_index, path_condition) for every leaf of the branch tree.
    let mut leaves: Vec<(usize, Vec<PureExpr>)> = Vec::new();
    if !collect_reborrow_leaves(body, &self_var, info, &mut Vec::new(), &mut leaves) {
        return vec![];
    }
    if leaves.is_empty() {
        return vec![];
    }

    let deref_self = PureExpr::Deref(Arc::new(self_var.clone()));
    let final_self = PureExpr::Final(Arc::new(self_var.clone()));
    let getf = |idx: usize, base: &PureExpr| PureExpr::LogicFnCall {
        name: format!("__trust_wp_tuple_get_{idx}"),
        args: vec![base.clone()],
    };

    let mut premises = Vec::with_capacity(info.field_count + 1);
    // Constructor preserved: discriminant(^self) == D.
    premises.push(PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(final_self.clone()),
            method: "discriminant".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(disc)),
    ));

    // Per-field: ¬touched_i ⇒ (^self).i == (*self).i.
    for field in 0..info.field_count {
        let touched: Vec<PureExpr> = leaves
            .iter()
            .filter(|(f, _)| *f == field)
            .map(|(_, path)| conjoin(path))
            .collect();
        let field_eq = PureExpr::BinOp(
            Arc::new(getf(field, &final_self)),
            BinOp::Eq,
            Arc::new(getf(field, &deref_self)),
        );
        if touched.is_empty() {
            // Never returned/recursed on any branch: unchanged unconditionally.
            premises.push(field_eq);
        } else {
            let touched_cond = disjoin(&touched);
            premises.push(PureExpr::BinOp(
                Arc::new(PureExpr::UnOp(UnOp::Not, Arc::new(touched_cond))),
                BinOp::Implies,
                Arc::new(field_eq),
            ));
        }
    }
    premises
}

/// Match `discriminant(*self) == D`, returning the `self` var and the
/// discriminant literal `D`.
fn match_discriminant_eq(expr: &PureExpr) -> Option<(PureExpr, i64)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    let (disc_call, disc_val) = match (lhs.as_ref(), rhs.as_ref()) {
        (PureExpr::MethodCall { .. }, PureExpr::Int(v)) => (lhs.as_ref(), *v),
        (PureExpr::Int(v), PureExpr::MethodCall { .. }) => (rhs.as_ref(), *v),
        _ => return None,
    };
    let PureExpr::MethodCall {
        receiver, method, ..
    } = disc_call
    else {
        return None;
    };
    if method != "discriminant" {
        return None;
    }
    // receiver = Deref(Var("self")); return the inner self var.
    let PureExpr::Deref(inner) = receiver.as_ref() else {
        return None;
    };
    if !matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "self") {
        return None;
    }
    Some(((**inner).clone(), disc_val))
}

/// Walk the branch tree, classifying each leaf as touching a specific enum
/// field under the accumulated path condition. Returns `false` (fail-closed) if
/// any leaf is not a direct field reborrow or a mapped recursion.
fn collect_reborrow_leaves(
    expr: &PureExpr,
    self_var: &PureExpr,
    info: &crate::mir_analysis::ReborrowProphecyInfo,
    path: &mut Vec<PureExpr>,
    out: &mut Vec<(usize, Vec<PureExpr>)>,
) -> bool {
    match expr {
        PureExpr::Ite(cond, then_b, else_b) => {
            path.push((**cond).clone());
            let ok_then = collect_reborrow_leaves(then_b, self_var, info, path, out);
            path.pop();
            if !ok_then {
                return false;
            }
            path.push(PureExpr::UnOp(UnOp::Not, Arc::new((**cond).clone())));
            let ok_else = collect_reborrow_leaves(else_b, self_var, info, path, out);
            path.pop();
            ok_else
        }
        PureExpr::LogicFnCall { name, args }
            if name.starts_with("__trust_wp_tuple_get_")
                && args.len() == 1
                && matches!(&args[0], PureExpr::Var(n, _) if n == "self") =>
        {
            let Some(idx) = name
                .strip_prefix("__trust_wp_tuple_get_")
                .and_then(|s| s.parse::<usize>().ok())
            else {
                return false;
            };
            if idx >= info.field_count {
                return false;
            }
            out.push((idx, path.clone()));
            true
        }
        PureExpr::Var(name, _) if name.starts_with("call_") => {
            let Some(local) = name
                .strip_prefix("call_")
                .and_then(|s| s.parse::<u32>().ok())
            else {
                return false;
            };
            match info.call_local_to_field.get(&local) {
                Some(&field) => {
                    out.push((field, path.clone()));
                    true
                }
                None => false,
            }
        }
        _ => false,
    }
}

/// Conjoin a list of boolean `PureExpr`s (empty ⇒ `true`).
fn conjoin(exprs: &[PureExpr]) -> PureExpr {
    let mut iter = exprs.iter().cloned();
    match iter.next() {
        None => PureExpr::Bool(true),
        Some(first) => iter.fold(first, |acc, e| {
            PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(e))
        }),
    }
}

/// Disjoin a list of boolean `PureExpr`s (empty ⇒ `false`).
fn disjoin(exprs: &[PureExpr]) -> PureExpr {
    let mut iter = exprs.iter().cloned();
    match iter.next() {
        None => PureExpr::Bool(false),
        Some(first) => iter.fold(first, |acc, e| {
            PureExpr::BinOp(Arc::new(acc), BinOp::Or, Arc::new(e))
        }),
    }
}
