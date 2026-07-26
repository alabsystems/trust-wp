// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Variable sort inference for SMT encoding.
//!
//! Infers whether free variables should be declared as Int, Bool, or Seq
//! based on how they are used in expressions.

use std::collections::{HashMap, HashSet};

use super::{
    context::{extract_pattern_bindings, SmtContext},
    sorts::VarSort,
    MAX_RECURSION_DEPTH,
};
use crate::formula::{BinOp, PureExpr, UnOp};

/// Infer variable sorts for free variables in an expression.
///
/// Variables used under logical operators (`!`, `&&`, `||`) are Bool.
/// Variables used in arithmetic or comparisons are Int.
/// If a variable is used in both contexts, defaults to Int.
///
/// **Note:** This returns original variable names. For transformed names
/// (like `old_x`, `x_view`), use [`collect_vars_with_sorts`] instead.
pub(crate) fn infer_var_sorts(expr: &PureExpr) -> HashMap<String, VarSort> {
    let mut sorts = HashMap::new();
    infer_var_sorts_inner(expr, VarSort::Bool, &mut sorts, 0);
    sorts
}

/// Collect all variables with their inferred sorts in a single AST traversal.
///
/// This combines variable collection and sort inference into one pass.
/// Variable names are transformed according to their context:
/// - `old(x)` → `old_x`
/// - `*v` → `v_current`
/// - `^v` → `v_final`
/// - `v@` → `v_view` (Seq sort)
///
/// Returns a `HashMap` mapping transformed variable names to their inferred sorts.
pub(crate) fn collect_vars_with_sorts(expr: &PureExpr) -> HashMap<String, VarSort> {
    let mut vars = HashMap::new();
    collect_vars_with_sorts_inner(expr, VarSort::Bool, SmtContext::Normal, &mut vars, 0);
    vars
}

#[allow(clippy::too_many_lines)]
fn collect_vars_with_sorts_inner(
    expr: &PureExpr,
    expected_sort: VarSort,
    var_ctx: SmtContext,
    vars: &mut HashMap<String, VarSort>,
    depth: usize,
) {
    if depth > MAX_RECURSION_DEPTH {
        return;
    }
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => {}
        PureExpr::Var(name, _) => {
            if !name.contains("::") {
                let transformed_name = match var_ctx {
                    SmtContext::Normal => name.clone(),
                    SmtContext::Old => format!("old_{name}"),
                };
                insert_var_sort(vars, transformed_name, expected_sort);
            }
        }
        PureExpr::BinOp(left, op, right) => {
            let operand_sort = match op {
                BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::DivTrunc
                | BinOp::RemTrunc
                | BinOp::Shl
                | BinOp::Shr
                | BinOp::BitAnd
                | BinOp::BitXor
                | BinOp::BitOr
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge => VarSort::Int,
                BinOp::Eq | BinOp::Ne => {
                    if is_bool_expr(left) || is_bool_expr(right) {
                        VarSort::Bool
                    } else {
                        VarSort::Int
                    }
                }
                BinOp::And | BinOp::Or | BinOp::Implies => VarSort::Bool,
            };
            collect_vars_with_sorts_inner(left, operand_sort, var_ctx, vars, depth + 1);
            collect_vars_with_sorts_inner(right, operand_sort, var_ctx, vars, depth + 1);
        }
        PureExpr::UnOp(op, operand) => {
            let operand_sort = match op {
                UnOp::Not => VarSort::Bool,
                UnOp::Neg | UnOp::BitNot => VarSort::Int,
            };
            collect_vars_with_sorts_inner(operand, operand_sort, var_ctx, vars, depth + 1);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_vars_with_sorts_inner(cond, VarSort::Bool, var_ctx, vars, depth + 1);
            collect_vars_with_sorts_inner(then_expr, expected_sort, var_ctx, vars, depth + 1);
            collect_vars_with_sorts_inner(else_expr, expected_sort, var_ctx, vars, depth + 1);
        }
        PureExpr::Old(inner) => {
            // For mutable borrow contracts: old(*v) = *v = v_current
            // For other expressions: old(x) uses "old_" prefix
            match inner.as_ref() {
                PureExpr::Deref(_) => {
                    // old(*v) creates same variables as *v (no old prefix needed)
                    collect_vars_with_sorts_inner(inner, expected_sort, var_ctx, vars, depth + 1);
                }
                _ => {
                    // old(x) switches to Old context for all nested variables
                    collect_vars_with_sorts_inner(
                        inner,
                        expected_sort,
                        SmtContext::Old,
                        vars,
                        depth + 1,
                    );
                }
            }
        }
        PureExpr::Deref(inner) => {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                let transformed = match var_ctx {
                    SmtContext::Normal => format!("{name}_current"),
                    SmtContext::Old => format!("old_{name}_current"),
                };
                insert_var_sort(vars, transformed, expected_sort);
            } else {
                collect_vars_with_sorts_inner(inner, expected_sort, var_ctx, vars, depth + 1);
            }
        }
        PureExpr::Final(inner) => {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                let transformed = match var_ctx {
                    SmtContext::Normal => format!("{name}_final"),
                    SmtContext::Old => format!("old_{name}_final"),
                };
                insert_var_sort(vars, transformed, expected_sort);
            } else {
                collect_vars_with_sorts_inner(inner, expected_sort, var_ctx, vars, depth + 1);
            }
        }
        PureExpr::View(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => {
                let transformed = match var_ctx {
                    SmtContext::Normal => format!("{name}_view"),
                    SmtContext::Old => format!("old_{name}_view"),
                };
                insert_var_sort(vars, transformed, VarSort::Seq);
            }
            PureExpr::Deref(deref_inner) => {
                if let PureExpr::Var(name, _) = deref_inner.as_ref() {
                    let transformed = match var_ctx {
                        SmtContext::Normal => format!("{name}_current_view"),
                        SmtContext::Old => format!("old_{name}_current_view"),
                    };
                    insert_var_sort(vars, transformed, VarSort::Seq);
                } else {
                    collect_vars_with_sorts_inner(inner, VarSort::Seq, var_ctx, vars, depth + 1);
                }
            }
            PureExpr::Final(final_inner) => {
                if let PureExpr::Var(name, _) = final_inner.as_ref() {
                    let transformed = match var_ctx {
                        SmtContext::Normal => format!("{name}_final_view"),
                        SmtContext::Old => format!("old_{name}_final_view"),
                    };
                    insert_var_sort(vars, transformed, VarSort::Seq);
                } else {
                    collect_vars_with_sorts_inner(inner, VarSort::Seq, var_ctx, vars, depth + 1);
                }
            }
            _ => {
                collect_vars_with_sorts_inner(inner, VarSort::Seq, var_ctx, vars, depth + 1);
            }
        },
        PureExpr::MethodCall { receiver, args, .. } => {
            collect_vars_with_sorts_inner(receiver, expected_sort, var_ctx, vars, depth + 1);
            for arg in args {
                collect_vars_with_sorts_inner(arg, VarSort::Int, var_ctx, vars, depth + 1);
            }
        }
        PureExpr::Forall {
            var,
            var_sort: _,
            body,
            triggers,
        }
        | PureExpr::Exists {
            var,
            var_sort: _,
            body,
            triggers,
        } => {
            // Temporarily track bound variable to avoid adding it as free
            let transformed_var = match var_ctx {
                SmtContext::Normal => var.clone(),
                SmtContext::Old => format!("old_{var}"),
            };
            let had_var = vars.contains_key(&transformed_var);
            collect_vars_with_sorts_inner(body, VarSort::Bool, var_ctx, vars, depth + 1);
            // Also collect from triggers
            for trigger in triggers {
                for expr in trigger {
                    collect_vars_with_sorts_inner(expr, VarSort::Int, var_ctx, vars, depth + 1);
                }
            }
            if !had_var {
                vars.remove(&transformed_var);
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_vars_with_sorts_inner(scrutinee, VarSort::Int, var_ctx, vars, depth + 1);
            for arm in arms {
                let mut bound = HashSet::new();
                extract_pattern_bindings(&arm.pattern, &mut bound);
                // Snapshot which pattern-bound names are already free from outer scope
                let pre_existing: HashSet<String> = bound
                    .iter()
                    .map(|b| match var_ctx {
                        SmtContext::Normal => b.clone(),
                        SmtContext::Old => format!("old_{b}"),
                    })
                    .filter(|t| vars.contains_key(t))
                    .collect();
                collect_vars_with_sorts_inner(&arm.body, expected_sort, var_ctx, vars, depth + 1);
                for b in bound {
                    let transformed = match var_ctx {
                        SmtContext::Normal => b,
                        SmtContext::Old => format!("old_{b}"),
                    };
                    if !pre_existing.contains(&transformed) {
                        vars.remove(&transformed);
                    }
                }
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                collect_vars_with_sorts_inner(arg, VarSort::Int, var_ctx, vars, depth + 1);
            }
        }
        PureExpr::Let { var, value, body } => {
            // FV(let x = e in body) = FV(e) ∪ (FV(body) \ {x})
            // The bound variable is NOT in scope for the value expression,
            // so we collect value vars first, then snapshot before body.
            let transformed_var = match var_ctx {
                SmtContext::Normal => var.clone(),
                SmtContext::Old => format!("old_{var}"),
            };
            collect_vars_with_sorts_inner(value, VarSort::Int, var_ctx, vars, depth + 1);
            let had_var = vars.contains_key(&transformed_var);
            collect_vars_with_sorts_inner(body, expected_sort, var_ctx, vars, depth + 1);
            if !had_var {
                vars.remove(&transformed_var);
            }
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_vars_with_sorts_inner(assumption, VarSort::Bool, var_ctx, vars, depth + 1);
            collect_vars_with_sorts_inner(body, expected_sort, var_ctx, vars, depth + 1);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_vars_with_sorts_inner(obligation, VarSort::Bool, var_ctx, vars, depth + 1);
            collect_vars_with_sorts_inner(body, expected_sort, var_ctx, vars, depth + 1);
        }
        PureExpr::Closure { params, body } => {
            // Track which closure-bound params already existed as free vars
            let had_params: Vec<(String, bool)> = params
                .iter()
                .map(|(name, _)| {
                    let transformed = match var_ctx {
                        SmtContext::Normal => name.clone(),
                        SmtContext::Old => format!("old_{name}"),
                    };
                    let had = vars.contains_key(&transformed);
                    (transformed, had)
                })
                .collect();
            collect_vars_with_sorts_inner(body, expected_sort, var_ctx, vars, depth + 1);
            // Remove closure-bound params that weren't free before
            for (transformed, had) in had_params {
                if !had {
                    vars.remove(&transformed);
                }
            }
        }
    }
}

/// Insert variable with sort, preferring Int if conflict
fn insert_var_sort(vars: &mut HashMap<String, VarSort>, name: String, sort: VarSort) {
    match vars.get(&name) {
        None => {
            vars.insert(name, sort);
        }
        Some(existing) if *existing != VarSort::Int && sort == VarSort::Int => {
            // Int wins if a variable appears in mixed contexts
            vars.insert(name, VarSort::Int);
        }
        _ => {}
    }
}

/// Infer sorts recursively, tracking expected sort from parent context.
#[allow(clippy::too_many_lines)]
fn infer_var_sorts_inner(
    expr: &PureExpr,
    expected: VarSort,
    sorts: &mut HashMap<String, VarSort>,
    depth: usize,
) {
    if depth > MAX_RECURSION_DEPTH {
        return;
    }
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => {}
        PureExpr::Var(name, _) => {
            if !name.contains("::") {
                match sorts.get(name) {
                    None => {
                        sorts.insert(name.clone(), expected);
                    }
                    Some(existing) => {
                        if *existing != VarSort::Int && expected == VarSort::Int {
                            // Int wins if a variable appears in mixed contexts.
                            sorts.insert(name.clone(), VarSort::Int);
                        }
                    }
                }
            }
        }
        PureExpr::BinOp(left, op, right) => {
            let operand_sort = match op {
                BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::DivTrunc
                | BinOp::RemTrunc
                | BinOp::Shl
                | BinOp::Shr
                | BinOp::BitAnd
                | BinOp::BitXor
                | BinOp::BitOr
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge => VarSort::Int,
                BinOp::Eq | BinOp::Ne => {
                    if is_bool_expr(left) || is_bool_expr(right) {
                        VarSort::Bool
                    } else {
                        VarSort::Int
                    }
                }
                BinOp::And | BinOp::Or | BinOp::Implies => VarSort::Bool,
            };
            infer_var_sorts_inner(left, operand_sort, sorts, depth + 1);
            infer_var_sorts_inner(right, operand_sort, sorts, depth + 1);
        }
        PureExpr::UnOp(op, operand) => {
            let operand_sort = match op {
                UnOp::Not => VarSort::Bool,
                UnOp::Neg | UnOp::BitNot => VarSort::Int,
            };
            infer_var_sorts_inner(operand, operand_sort, sorts, depth + 1);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            infer_var_sorts_inner(cond, VarSort::Bool, sorts, depth + 1);
            infer_var_sorts_inner(then_expr, expected, sorts, depth + 1);
            infer_var_sorts_inner(else_expr, expected, sorts, depth + 1);
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            infer_var_sorts_inner(inner, expected, sorts, depth + 1);
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            infer_var_sorts_inner(receiver, expected, sorts, depth + 1);
            for arg in args {
                infer_var_sorts_inner(arg, VarSort::Int, sorts, depth + 1);
            }
        }
        PureExpr::Forall {
            var,
            var_sort: _,
            body,
            triggers,
        }
        | PureExpr::Exists {
            var,
            var_sort: _,
            body,
            triggers,
        } => {
            let had_var = sorts.contains_key(var);
            infer_var_sorts_inner(body, VarSort::Bool, sorts, depth + 1);
            for trigger in triggers {
                for expr in trigger {
                    infer_var_sorts_inner(expr, VarSort::Int, sorts, depth + 1);
                }
            }
            if !had_var {
                sorts.remove(var);
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            infer_var_sorts_inner(scrutinee, VarSort::Int, sorts, depth + 1);
            for arm in arms {
                let mut bound = HashSet::new();
                extract_pattern_bindings(&arm.pattern, &mut bound);
                let pre_existing: HashSet<String> = bound
                    .iter()
                    .filter(|b| sorts.contains_key(b.as_str()))
                    .cloned()
                    .collect();
                infer_var_sorts_inner(&arm.body, expected, sorts, depth + 1);
                for b in bound {
                    if !pre_existing.contains(&b) {
                        sorts.remove(&b);
                    }
                }
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                infer_var_sorts_inner(arg, VarSort::Int, sorts, depth + 1);
            }
        }
        PureExpr::Let { var, value, body } => {
            infer_var_sorts_inner(value, VarSort::Int, sorts, depth + 1);
            let had_var = sorts.contains_key(var);
            infer_var_sorts_inner(body, expected, sorts, depth + 1);
            if !had_var {
                sorts.remove(var);
            }
        }
        PureExpr::LetAssume { assumption, body } => {
            infer_var_sorts_inner(assumption, VarSort::Bool, sorts, depth + 1);
            infer_var_sorts_inner(body, expected, sorts, depth + 1);
        }
        PureExpr::LetObligation { obligation, body } => {
            infer_var_sorts_inner(obligation, VarSort::Bool, sorts, depth + 1);
            infer_var_sorts_inner(body, expected, sorts, depth + 1);
        }
        PureExpr::Closure { params, body } => {
            let had_params: Vec<(String, bool)> = params
                .iter()
                .map(|(name, _)| (name.clone(), sorts.contains_key(name)))
                .collect();
            infer_var_sorts_inner(body, expected, sorts, depth + 1);
            for (name, had) in had_params {
                if !had {
                    sorts.remove(&name);
                }
            }
        }
    }
}

/// Infer variable sorts from multiple expressions, merging the results.
#[cfg(test)]
pub(crate) fn infer_var_sorts_multi(exprs: &[PureExpr]) -> HashMap<String, VarSort> {
    let mut sorts = HashMap::new();
    for expr in exprs {
        infer_var_sorts_inner(expr, VarSort::Bool, &mut sorts, 0);
    }
    sorts
}

/// Check if an expression is a boolean expression (literal, variable under Bool, or logical op).
/// Used to detect `flag == true` patterns where both operands should be Bool.
pub(super) fn is_bool_expr(expr: &PureExpr) -> bool {
    match expr {
        // Bool literals, logical operations (not, and, or, =>), and comparisons produce Bool
        PureExpr::Bool(_)
        | PureExpr::UnOp(UnOp::Not, _)
        | PureExpr::BinOp(
            _,
            BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge,
            _,
        ) => true,
        // Eq/Ne could be either Int or Bool equality, other expressions are not Bool
        _ => false,
    }
}

/// Check if a variable name should have Seq sort (Part of #111)
///
/// Variables ending in `_view` are logical sequence views (from View expressions).
/// These include: `self_view`, `v_current_view`, `v_final_view`, etc.
pub(crate) fn is_seq_var(name: &str) -> bool {
    name.ends_with("_view")
}
