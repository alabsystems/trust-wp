// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Variable collection walkers for SMT encoding.
//!
//! Collects free variable names from expressions and formulas, applying
//! RustHorn-style name transformations (old_, _current, _final, _view).

use std::collections::HashSet;

use super::{context::extract_pattern_bindings, MAX_RECURSION_DEPTH};
use crate::formula::{Formula, PureExpr};

/// Collect all variable names used in an expression
pub(crate) fn collect_vars_expr(expr: &PureExpr) -> HashSet<String> {
    let mut vars = HashSet::new();
    collect_vars_expr_inner(expr, &mut vars, 0);
    vars
}

#[allow(clippy::too_many_lines)]
fn collect_vars_expr_inner(expr: &PureExpr, vars: &mut HashSet<String>, depth: usize) {
    if depth > MAX_RECURSION_DEPTH {
        return;
    }
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => {}
        PureExpr::Var(name, _) => {
            // Don't count Rust constants as variables
            if !name.contains("::") {
                vars.insert(name.clone());
            }
        }
        PureExpr::BinOp(left, _, right) => {
            collect_vars_expr_inner(left, vars, depth + 1);
            collect_vars_expr_inner(right, vars, depth + 1);
        }
        PureExpr::UnOp(_, operand) => {
            collect_vars_expr_inner(operand, vars, depth + 1);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_vars_expr_inner(cond, vars, depth + 1);
            collect_vars_expr_inner(then_expr, vars, depth + 1);
            collect_vars_expr_inner(else_expr, vars, depth + 1);
        }
        PureExpr::Old(inner) => {
            // For mutable borrow contracts: old(*v) = *v = v_current
            // For other expressions: old(x) uses "old_" prefix
            match inner.as_ref() {
                PureExpr::Deref(_) => {
                    // old(*v) creates same variables as *v
                    collect_vars_expr_inner(inner, vars, depth + 1);
                }
                _ => {
                    // For old(x), we need to declare old_x as a separate variable
                    collect_old_vars_expr(inner, vars, depth + 1);
                }
            }
        }
        PureExpr::Deref(inner) => {
            // *v creates {v}_current variable
            if let PureExpr::Var(name, _) = inner.as_ref() {
                vars.insert(format!("{name}_current"));
            } else {
                collect_vars_expr_inner(inner, vars, depth + 1);
            }
        }
        PureExpr::Final(inner) => {
            // ^v creates {v}_final variable
            if let PureExpr::Var(name, _) = inner.as_ref() {
                vars.insert(format!("{name}_final"));
            } else {
                collect_vars_expr_inner(inner, vars, depth + 1);
            }
        }
        PureExpr::View(inner) => {
            // expr@ creates {expr}_view variable
            // Must match expr_to_smt encoding exactly
            match inner.as_ref() {
                PureExpr::Var(name, _) => {
                    vars.insert(format!("{name}_view"));
                }
                PureExpr::Deref(deref_inner) => {
                    // (*v)@ = v_current_view
                    if let PureExpr::Var(name, _) = deref_inner.as_ref() {
                        vars.insert(format!("{name}_current_view"));
                    } else {
                        collect_vars_expr_inner(inner, vars, depth + 1);
                    }
                }
                PureExpr::Final(final_inner) => {
                    // (^v)@ = v_final_view
                    if let PureExpr::Var(name, _) = final_inner.as_ref() {
                        vars.insert(format!("{name}_final_view"));
                    } else {
                        collect_vars_expr_inner(inner, vars, depth + 1);
                    }
                }
                _ => {
                    collect_vars_expr_inner(inner, vars, depth + 1);
                }
            }
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            // Collect from receiver and all arguments
            collect_vars_expr_inner(receiver, vars, depth + 1);
            for arg in args {
                collect_vars_expr_inner(arg, vars, depth + 1);
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
            // Preserve outer free vars: only remove the bound variable if it
            // wasn't already free from a sibling expression (same pattern as Let).
            let had_var = vars.contains(var.as_str());
            collect_vars_expr_inner(body, vars, depth + 1);
            for trigger in triggers {
                for expr in trigger {
                    collect_vars_expr_inner(expr, vars, depth + 1);
                }
            }
            if !had_var {
                vars.remove(var);
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_vars_expr_inner(scrutinee, vars, depth + 1);
            for arm in arms {
                let mut bound = HashSet::new();
                extract_pattern_bindings(&arm.pattern, &mut bound);
                // Snapshot which pattern-bound names are already free from outer scope
                let pre_existing: HashSet<String> = bound
                    .iter()
                    .filter(|b| vars.contains(b.as_str()))
                    .cloned()
                    .collect();
                collect_vars_expr_inner(&arm.body, vars, depth + 1);
                for b in bound {
                    if !pre_existing.contains(&b) {
                        vars.remove(&b);
                    }
                }
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            // Collect vars from all arguments
            for arg in args {
                collect_vars_expr_inner(arg, vars, depth + 1);
            }
        }
        PureExpr::Let { var, value, body } => {
            // FV(let x = e in body) = FV(e) ∪ (FV(body) \ {x})
            collect_vars_expr_inner(value, vars, depth + 1);
            let had_var = vars.contains(var.as_str());
            collect_vars_expr_inner(body, vars, depth + 1);
            if !had_var {
                vars.remove(var);
            }
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_vars_expr_inner(assumption, vars, depth + 1);
            collect_vars_expr_inner(body, vars, depth + 1);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_vars_expr_inner(obligation, vars, depth + 1);
            collect_vars_expr_inner(body, vars, depth + 1);
        }
        PureExpr::Closure { params, body } => {
            // Preserve outer free vars with the same name as closure params.
            let outer_flags: Vec<bool> = params
                .iter()
                .map(|(name, _)| vars.contains(name.as_str()))
                .collect();
            collect_vars_expr_inner(body, vars, depth + 1);
            for ((name, _), had) in params.iter().zip(outer_flags.iter()) {
                if !had {
                    vars.remove(name);
                }
            }
        }
    }
}

/// Collect `old_`-prefixed variable names from an expression inside `old()`
#[allow(clippy::too_many_lines)]
fn collect_old_vars_expr(expr: &PureExpr, vars: &mut HashSet<String>, depth: usize) {
    if depth > MAX_RECURSION_DEPTH {
        return;
    }
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => {}
        PureExpr::Var(name, _) => {
            if !name.contains("::") {
                vars.insert(format!("old_{name}"));
            }
        }
        PureExpr::BinOp(left, _, right) => {
            collect_old_vars_expr(left, vars, depth + 1);
            collect_old_vars_expr(right, vars, depth + 1);
        }
        PureExpr::UnOp(_, operand) => {
            collect_old_vars_expr(operand, vars, depth + 1);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_old_vars_expr(cond, vars, depth + 1);
            collect_old_vars_expr(then_expr, vars, depth + 1);
            collect_old_vars_expr(else_expr, vars, depth + 1);
        }
        PureExpr::Old(inner) => {
            // Nested old - just continue collecting
            collect_old_vars_expr(inner, vars, depth + 1);
        }
        PureExpr::Deref(inner) => {
            // *v in old context creates old_{v}_current
            if let PureExpr::Var(name, _) = inner.as_ref() {
                vars.insert(format!("old_{name}_current"));
            } else {
                collect_old_vars_expr(inner, vars, depth + 1);
            }
        }
        PureExpr::Final(inner) => {
            // ^v in old context creates old_{v}_final
            if let PureExpr::Var(name, _) = inner.as_ref() {
                vars.insert(format!("old_{name}_final"));
            } else {
                collect_old_vars_expr(inner, vars, depth + 1);
            }
        }
        PureExpr::View(inner) => {
            // expr@ in old context: {expr_in_old_context}_view
            // Must match expr_to_smt_with_old_prefix encoding exactly
            // For (*v)@: old_v_current_view (via Deref giving old_v_current + _view suffix)
            // For (^v)@: old_v_final_view (via Final giving old_v_final + _view suffix)
            match inner.as_ref() {
                PureExpr::Var(name, _) => {
                    vars.insert(format!("old_{name}_view"));
                }
                PureExpr::Deref(deref_inner) => {
                    if let PureExpr::Var(name, _) = deref_inner.as_ref() {
                        vars.insert(format!("old_{name}_current_view"));
                    } else {
                        collect_old_vars_expr(inner, vars, depth + 1);
                    }
                }
                PureExpr::Final(final_inner) => {
                    if let PureExpr::Var(name, _) = final_inner.as_ref() {
                        vars.insert(format!("old_{name}_final_view"));
                    } else {
                        collect_old_vars_expr(inner, vars, depth + 1);
                    }
                }
                _ => {
                    collect_old_vars_expr(inner, vars, depth + 1);
                }
            }
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            // Collect from receiver and all arguments in old context
            collect_old_vars_expr(receiver, vars, depth + 1);
            for arg in args {
                collect_old_vars_expr(arg, vars, depth + 1);
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
            let old_var = format!("old_{var}");
            let had_var = vars.contains(&old_var);
            collect_old_vars_expr(body, vars, depth + 1);
            for trigger in triggers {
                for expr in trigger {
                    collect_old_vars_expr(expr, vars, depth + 1);
                }
            }
            if !had_var {
                vars.remove(&old_var);
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_old_vars_expr(scrutinee, vars, depth + 1);
            for arm in arms {
                let mut bound = HashSet::new();
                extract_pattern_bindings(&arm.pattern, &mut bound);
                let pre_existing: HashSet<String> = bound
                    .iter()
                    .map(|b| format!("old_{b}"))
                    .filter(|ob| vars.contains(ob))
                    .collect();
                collect_old_vars_expr(&arm.body, vars, depth + 1);
                for b in bound {
                    let old_b = format!("old_{b}");
                    if !pre_existing.contains(&old_b) {
                        vars.remove(&old_b);
                    }
                }
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            // Collect vars from all arguments in old context
            for arg in args {
                collect_old_vars_expr(arg, vars, depth + 1);
            }
        }
        PureExpr::Let { var, value, body } => {
            // FV(let x = e in body) = FV(e) ∪ (FV(body) \ {x})
            let old_var = format!("old_{var}");
            collect_old_vars_expr(value, vars, depth + 1);
            let had_var = vars.contains(&old_var);
            collect_old_vars_expr(body, vars, depth + 1);
            if !had_var {
                vars.remove(&old_var);
            }
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_old_vars_expr(assumption, vars, depth + 1);
            collect_old_vars_expr(body, vars, depth + 1);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_old_vars_expr(obligation, vars, depth + 1);
            collect_old_vars_expr(body, vars, depth + 1);
        }
        PureExpr::Closure { params, body } => {
            let outer_flags: Vec<(String, bool)> = params
                .iter()
                .map(|(name, _)| {
                    let old_name = format!("old_{name}");
                    let had = vars.contains(&old_name);
                    (old_name, had)
                })
                .collect();
            collect_old_vars_expr(body, vars, depth + 1);
            for (old_name, had) in &outer_flags {
                if !had {
                    vars.remove(old_name);
                }
            }
        }
    }
}

/// Collect all variable names used in a formula
pub(crate) fn collect_vars_formula(formula: &Formula) -> HashSet<String> {
    let mut vars = HashSet::new();
    collect_vars_formula_inner(formula, &mut vars, 0);
    vars
}

fn collect_vars_formula_inner(formula: &Formula, vars: &mut HashSet<String>, depth: usize) {
    if depth > MAX_RECURSION_DEPTH {
        return;
    }
    match formula {
        Formula::True | Formula::False => {}
        Formula::Pure(expr) => {
            vars.extend(collect_vars_expr(expr));
        }
        Formula::And(l, r)
        | Formula::Or(l, r)
        | Formula::Implies(l, r)
        | Formula::SepConj(l, r)
        | Formula::MagicWand(l, r) => {
            collect_vars_formula_inner(l, vars, depth + 1);
            collect_vars_formula_inner(r, vars, depth + 1);
        }
        Formula::Forall {
            var,
            body,
            triggers,
            ..
        }
        | Formula::Exists {
            var,
            body,
            triggers,
            ..
        } => {
            let had_var = vars.contains(var.as_str());
            collect_vars_formula_inner(body, vars, depth + 1);
            for pattern in triggers {
                for trigger in pattern {
                    collect_vars_formula_inner(trigger, vars, depth + 1);
                }
            }
            if !had_var {
                vars.remove(var);
            }
        }
        Formula::PointsTo {
            location, value, ..
        } => {
            vars.insert(location.0.clone());
            if let crate::formula::Value::Expr(e) = value {
                vars.extend(collect_vars_expr(e));
            }
        }
        Formula::MutBorrow {
            var,
            current,
            final_val,
            id,
        } => {
            // MutBorrow creates {var}_current, {var}_final, and {var}_id variables.
            vars.insert(format!("{var}_current"));
            vars.insert(format!("{var}_final"));
            vars.insert(format!("{var}_id"));
            // Also collect any variables used in the expressions
            vars.extend(collect_vars_expr(current));
            vars.extend(collect_vars_expr(final_val));
            vars.extend(collect_vars_expr(id));
        }
    }
}
