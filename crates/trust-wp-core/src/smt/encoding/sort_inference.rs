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
use crate::formula::{BinOp, MatchArm, PureExpr, UnOp};

/// Infer variable sorts for free variables in an expression.
///
/// Variables used under logical operators (`!`, `&&`, `||`) are Bool.
/// Variables used in arithmetic or comparisons are Int.
/// If a variable is used in both contexts, defaults to Int.
///
/// **Note:** This returns original variable names, so it must not be used to
/// emit declarations — the printer spells the same variables `old_x`, `x_view`,
/// `v_current`. [`collect_vars_with_sorts`] is the one that matches the
/// printer, and is what [`super::generator::SmtGenerator`] uses. What survives
/// here is the context-propagation rule those tests pin down.
#[cfg(test)]
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
            // A var-rooted `old(...)` has one name the printer will spell; take
            // it. Everything else keeps the structural walk below.
            if let Some(name) = printed_var_name(expr, var_ctx, depth) {
                let sort = if name.ends_with("_view") {
                    view_sort(sort_annotation(expr, depth + 1))
                } else {
                    expected_sort
                };
                insert_var_sort(vars, name, sort);
                return;
            }
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
        // One rule for every RustHorn wrapper chain, taken from the printer
        // itself rather than re-enumerated shape by shape: whatever
        // `write_expr_ctx` will spell this expression, declare THAT name.
        PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            match printed_var_name(expr, var_ctx, depth) {
                Some(name) => insert_var_sort(vars, name, expected_sort),
                None => {
                    collect_vars_with_sorts_inner(inner, expected_sort, var_ctx, vars, depth + 1);
                }
            }
        }
        PureExpr::View(inner) => match printed_var_name(expr, var_ctx, depth) {
            Some(name) => {
                let sort = view_sort(sort_annotation(inner, depth + 1));
                insert_var_sort(vars, name, sort);
            }
            None => collect_vars_with_sorts_inner(inner, VarSort::Seq, var_ctx, vars, depth + 1),
        },
        PureExpr::MethodCall { receiver, args, .. } => {
            // The receiver is a VALUE, not the call's result. Handing it
            // `expected_sort` declared `(*f)` as `Bool` wherever the call sat
            // in a formula — `(precondition f_current x)` — while the same
            // carrier came out `Int` at another use, and the query then applied
            // one uninterpreted function to both. `Int` is the default
            // `VarSort::from_expr_sort` gives an opaque carrier, so it is the
            // one that agrees. A `v@` receiver is unaffected: the View arm
            // reads its sort from the annotation, not from here.
            collect_vars_with_sorts_inner(receiver, VarSort::Int, var_ctx, vars, depth + 1);
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
#[cfg(test)]
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

/// The SMT sort of `x@` given `x`'s own annotated sort.
///
/// The logical view of a collection is a sequence, which is the interesting
/// case and the historical default. The view of a *scalar* is that same scalar
/// — `x@` for an `i32` is the mathematical integer behind it, and the driver
/// leans on exactly that when it injects `x@ >= i32::MIN` range preconditions
/// (`callbacks/integer_range.rs`: "Use View to get the mathematical model
/// (identity for integers)"). Declaring those as `Seq` produced queries no
/// solver would accept. An unannotated variable keeps the sequence default:
/// nothing in the expression says otherwise, and collections are why the view
/// operator exists.
fn view_sort(sort: Option<&crate::formula::ExprSort>) -> VarSort {
    use crate::formula::ExprSort;
    match sort.map(peel_references) {
        Some(ExprSort::Int | ExprSort::Float(_)) => VarSort::Int,
        Some(ExprSort::Bool) => VarSort::Bool,
        _ => VarSort::Seq,
    }
}

/// Look through `p @ pat` aliases to the pattern that decides the tester.
fn strip_pattern_aliases(pattern: &crate::formula::Pattern) -> &crate::formula::Pattern {
    let mut current = pattern;
    while let crate::formula::Pattern::Alias { pattern, .. } = current {
        current = pattern;
    }
    current
}

/// Look through `&T` / `&mut T` to the referent's sort.
fn peel_references(sort: &crate::formula::ExprSort) -> &crate::formula::ExprSort {
    use crate::formula::ExprSort;
    let mut current = sort;
    while let ExprSort::Ref(inner) | ExprSort::MutRef(inner) = current {
        current = inner;
    }
    current
}

/// True when an expression stands for a *formula* — something an `assert` can
/// take directly — rather than for a term.
///
/// Deliberately conservative and syntactic: it answers yes only for shapes that
/// can only be formulas. Anything it is unsure about is a term, which is the
/// safe direction for its one caller (hoisting side conditions out of term
/// position in the `--emit-smt` renderer): a mistaken "term" there produces a
/// well-sorted query with one extra top-level assumption, while a mistaken
/// "formula" leaves the ill-sorted `(=> Bool Int)` the hoist exists to remove.
pub(crate) fn is_formula_shaped(expr: &PureExpr) -> bool {
    is_formula_shaped_at(expr, 0)
}

fn is_formula_shaped_at(expr: &PureExpr, depth: usize) -> bool {
    if depth > MAX_RECURSION_DEPTH {
        return false;
    }
    match expr {
        PureExpr::Bool(_) => true,
        PureExpr::UnOp(UnOp::Not, _) => true,
        PureExpr::BinOp(_, op, _) => matches!(
            op,
            BinOp::And
                | BinOp::Or
                | BinOp::Implies
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::Eq
                | BinOp::Ne
        ),
        PureExpr::Forall { .. } | PureExpr::Exists { .. } => true,
        // These print as a wrapper around their body, so they are whatever
        // their body is.
        PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. }
        | PureExpr::Let { body, .. } => is_formula_shaped_at(body, depth + 1),
        PureExpr::Ite(_, then_expr, else_expr) => {
            is_formula_shaped_at(then_expr, depth + 1) && is_formula_shaped_at(else_expr, depth + 1)
        }
        _ => false,
    }
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

// ---------------------------------------------------------------------------
// Applied symbols
// ---------------------------------------------------------------------------

/// A symbol the printer *applies* — `(logic_inv v)`, `(seq_len s)` — as opposed
/// to a variable it merely names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AppliedSymbol {
    /// The symbol as `write_expr_ctx` spells it.
    pub(crate) name: String,
    /// One sort per argument, in order.
    pub(crate) params: Vec<VarSort>,
    /// The sort the symbol is used at.
    pub(crate) result: VarSort,
}

/// True for symbols one of the generated preambles already declares.
///
/// `generate_seq_preamble` declares the `seq_*` family, `generate_heap_preamble`
/// the `heap_*` family, and `generate_bitwise_preamble` the integer bitwise UFs.
/// Re-declaring any of them would make the query illegal a second way.
fn is_preamble_symbol(name: &str) -> bool {
    // `generate_bitwise_preamble` declares exactly the five BINARY bitwise UFs
    // (`BinOp::smt_int_uf_name`). `__trust_wp_bit_not` is emitted by the
    // printer for `UnOp::BitNot` and declared by nobody, so it must NOT be
    // filtered out here — it is one of the symbols this pass exists to catch.
    name.starts_with("seq_")
        || name.starts_with("heap_")
        || [
            BinOp::Shl,
            BinOp::Shr,
            BinOp::BitAnd,
            BinOp::BitXor,
            BinOp::BitOr,
        ]
        .into_iter()
        .filter_map(BinOp::smt_int_uf_name)
        .any(|uf| uf == name)
}

/// Collect every applied symbol in an expression, with the sorts it is used at.
///
/// A verification condition may mention logic functions, type-invariant
/// predicates and user methods that no preamble declares. Emitting the query
/// without declaring them produces text no SMT solver will parse, which defeats
/// the point of `--emit-smt`. Sorts come from how each position is *used* —
/// the same rule the variable declarations follow — so the result is a query
/// that parses and reads the way the encoder meant it.
pub(crate) fn collect_applied_symbols(
    expr: &PureExpr,
    used_at: VarSort,
    declared: &HashMap<String, VarSort>,
) -> Vec<AppliedSymbol> {
    let mut found = Vec::new();
    collect_applied_symbols_inner(expr, used_at, declared, &mut found, 0);
    found
}

/// The name the printer emits for a variable-shaped expression, if it is one.
///
/// An exact mirror of `write_var` / `write_old` / `write_deref` / `write_final`
/// / `write_view` in `expr_printer`, including their wrapper chains: the
/// printer appends a suffix per wrapper, so `Deref(Final(f))` is
/// `f_final_current` and `View(Deref(v))` is `v_current_view`. Matching only
/// the single-wrapper shapes left those chained names undeclared.
///
/// `None` for anything not rooted at a plain variable — a path constant like
/// `i32::MAX` prints as a literal, and a wrapper over a call prints as that
/// call with a suffix, which is not a declarable symbol.
pub(crate) fn printed_var_name(expr: &PureExpr, ctx: SmtContext, depth: usize) -> Option<String> {
    if depth > MAX_RECURSION_DEPTH {
        return None;
    }
    match expr {
        PureExpr::Var(name, _) if !name.contains("::") => Some(match ctx {
            SmtContext::Normal => name.clone(),
            SmtContext::Old => format!("old_{name}"),
        }),
        // `old(*v)` is `*v`: the deref already names the entry-state value.
        PureExpr::Old(inner) => match (ctx, inner.as_ref()) {
            (SmtContext::Normal, PureExpr::Deref(_)) => {
                printed_var_name(inner, SmtContext::Normal, depth + 1)
            }
            _ => printed_var_name(inner, SmtContext::Old, depth + 1),
        },
        PureExpr::Deref(inner) => Some(format!(
            "{}_current",
            printed_var_name(inner, ctx, depth + 1)?
        )),
        PureExpr::Final(inner) => Some(format!(
            "{}_final",
            printed_var_name(inner, ctx, depth + 1)?
        )),
        PureExpr::View(inner) => Some(format!("{}_view", printed_var_name(inner, ctx, depth + 1)?)),
        _ => None,
    }
}

fn printed_name(expr: &PureExpr) -> Option<String> {
    printed_var_name(expr, SmtContext::Normal, 0)
}

/// The sort an argument will be declared at, preferring the declaration map.
fn argument_sort(expr: &PureExpr, declared: &HashMap<String, VarSort>) -> VarSort {
    printed_name(expr)
        .and_then(|name| declared.get(&name).copied())
        .unwrap_or_else(|| printed_sort(expr))
}

/// The sort an expression is printed at, judged from its shape.
///
/// Deliberately shallow: it decides argument sorts, and every sort it cannot
/// read off the syntax is `Int`, which is the same default
/// [`VarSort::from_expr_sort`] applies to an opaque datatype.
fn printed_sort(expr: &PureExpr) -> VarSort {
    printed_sort_at(expr, 0)
}

fn printed_sort_at(expr: &PureExpr, depth: usize) -> VarSort {
    if depth > MAX_RECURSION_DEPTH {
        return VarSort::Int;
    }
    match expr {
        PureExpr::Bool(_) => VarSort::Bool,
        PureExpr::Var(_, sort) => VarSort::from_expr_sort(sort.as_ref()),
        PureExpr::View(inner) => view_sort(sort_annotation(inner, depth + 1)),
        PureExpr::UnOp(UnOp::Not, _) => VarSort::Bool,
        PureExpr::BinOp(left, op, _) => match op {
            BinOp::And
            | BinOp::Or
            | BinOp::Implies
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::Eq
            | BinOp::Ne => VarSort::Bool,
            _ => printed_sort_at(left, depth + 1),
        },
        _ => VarSort::Int,
    }
}

/// The sort annotation on a variable, looking through the RustHorn wrappers.
fn sort_annotation(expr: &PureExpr, depth: usize) -> Option<&crate::formula::ExprSort> {
    if depth > MAX_RECURSION_DEPTH {
        return None;
    }
    match expr {
        PureExpr::Var(_, sort) => sort.as_ref(),
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner) => sort_annotation(inner, depth + 1),
        _ => None,
    }
}

fn record(found: &mut Vec<AppliedSymbol>, symbol: AppliedSymbol) {
    if is_preamble_symbol(&symbol.name) {
        return;
    }
    if found.iter().any(|existing| existing.name == symbol.name) {
        return;
    }
    found.push(symbol);
}

/// Record the symbol a method call applies, then walk its receiver and args.
///
/// The receiver is the first parameter — `xs.get(i)` prints as `(get xs i)` —
/// so the declared signature has to lead with the receiver's sort.
fn collect_from_method_call(
    receiver: &PureExpr,
    method: &str,
    args: &[PureExpr],
    expected: VarSort,
    declared: &HashMap<String, VarSort>,
    found: &mut Vec<AppliedSymbol>,
    depth: usize,
) {
    let mut params = vec![argument_sort(receiver, declared)];
    params.extend(args.iter().map(|arg| argument_sort(arg, declared)));
    record(
        found,
        AppliedSymbol {
            name: super::expr_printer::method_smt_name(method).to_string(),
            params,
            result: expected,
        },
    );
    collect_applied_symbols_inner(receiver, VarSort::Int, declared, found, depth + 1);
    for arg in args {
        collect_applied_symbols_inner(arg, printed_sort(arg), declared, found, depth + 1);
    }
}

/// Record the symbol a logic-function call applies, then walk its arguments.
fn collect_from_logic_fn_call(
    name: &str,
    args: &[PureExpr],
    expected: VarSort,
    declared: &HashMap<String, VarSort>,
    found: &mut Vec<AppliedSymbol>,
    depth: usize,
) {
    record(
        found,
        AppliedSymbol {
            name: crate::logic::logic_fn_smt_name(name),
            params: args
                .iter()
                .map(|arg| argument_sort(arg, declared))
                .collect(),
            result: expected,
        },
    );
    for arg in args {
        collect_applied_symbols_inner(arg, printed_sort(arg), declared, found, depth + 1);
    }
}

/// The sort both operands of a binary operator are read at.
///
/// `=` and `!=` are the only polymorphic ones: they take the sort of whichever
/// side reveals it, falling back to `Int`.
fn binop_operand_sort(left: &PureExpr, op: BinOp, right: &PureExpr) -> VarSort {
    match op {
        BinOp::And | BinOp::Or | BinOp::Implies => VarSort::Bool,
        BinOp::Eq | BinOp::Ne => {
            if is_bool_expr(left) || is_bool_expr(right) {
                VarSort::Bool
            } else {
                match printed_sort(left) {
                    VarSort::Int => printed_sort(right),
                    sort => sort,
                }
            }
        }
        _ => VarSort::Int,
    }
}

/// Record the constructor testers a match lowers to, then walk scrutinee, arm
/// literals and arm bodies.
fn collect_from_match(
    scrutinee: &PureExpr,
    arms: &[MatchArm],
    expected: VarSort,
    declared: &HashMap<String, VarSort>,
    found: &mut Vec<AppliedSymbol>,
    depth: usize,
) {
    let scrutinee_sort = argument_sort(scrutinee, declared);
    collect_applied_symbols_inner(scrutinee, VarSort::Int, declared, found, depth + 1);
    for arm in arms {
        // `write_match_ite` turns a constructor pattern into an applied
        // tester over the scrutinee — `(is_some opt)`, `(is_<ctor> x)`.
        // Those are symbols the query uses, so they need declaring too.
        if let crate::formula::Pattern::Constructor { name, .. } =
            strip_pattern_aliases(&arm.pattern)
        {
            let tester = match name.as_str() {
                "Some" | "None" => "is_some".to_string(),
                other => format!("is_{}", other.to_lowercase()),
            };
            record(
                found,
                AppliedSymbol {
                    name: tester,
                    params: vec![scrutinee_sort],
                    result: VarSort::Bool,
                },
            );
        }
        if let crate::formula::Pattern::Literal(literal) = strip_pattern_aliases(&arm.pattern) {
            collect_applied_symbols_inner(literal, scrutinee_sort, declared, found, depth + 1);
        }
        collect_applied_symbols_inner(&arm.body, expected, declared, found, depth + 1);
    }
}

fn collect_applied_symbols_inner(
    expr: &PureExpr,
    expected: VarSort,
    declared: &HashMap<String, VarSort>,
    found: &mut Vec<AppliedSymbol>,
    depth: usize,
) {
    if depth > MAX_RECURSION_DEPTH {
        return;
    }
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => collect_from_method_call(receiver, method, args, expected, declared, found, depth),
        PureExpr::LogicFnCall { name, args } => {
            collect_from_logic_fn_call(name, args, expected, declared, found, depth);
        }
        PureExpr::BinOp(left, op, right) => {
            let operand = binop_operand_sort(left, *op, right);
            collect_applied_symbols_inner(left, operand, declared, found, depth + 1);
            collect_applied_symbols_inner(right, operand, declared, found, depth + 1);
        }
        PureExpr::UnOp(op, operand) => {
            let sort = match op {
                UnOp::Not => VarSort::Bool,
                UnOp::Neg | UnOp::BitNot => VarSort::Int,
            };
            // `!x` on an integer prints as `(__trust_wp_bit_not x)`, and unlike
            // the binary bitwise operators no preamble declares it.
            if matches!(op, UnOp::BitNot) {
                record(
                    found,
                    AppliedSymbol {
                        name: "__trust_wp_bit_not".to_string(),
                        params: vec![argument_sort(operand, declared)],
                        result: VarSort::Int,
                    },
                );
            }
            collect_applied_symbols_inner(operand, sort, declared, found, depth + 1);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_applied_symbols_inner(cond, VarSort::Bool, declared, found, depth + 1);
            collect_applied_symbols_inner(then_expr, expected, declared, found, depth + 1);
            collect_applied_symbols_inner(else_expr, expected, declared, found, depth + 1);
        }
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            collect_applied_symbols_inner(inner, expected, declared, found, depth + 1);
        }
        PureExpr::View(inner) => {
            collect_applied_symbols_inner(inner, VarSort::Seq, declared, found, depth + 1);
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            collect_applied_symbols_inner(body, VarSort::Bool, declared, found, depth + 1);
            for trigger in triggers {
                for term in trigger {
                    collect_applied_symbols_inner(term, VarSort::Int, declared, found, depth + 1);
                }
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_from_match(scrutinee, arms, expected, declared, found, depth);
        }
        PureExpr::Let { value, body, .. } => {
            collect_applied_symbols_inner(value, VarSort::Int, declared, found, depth + 1);
            collect_applied_symbols_inner(body, expected, declared, found, depth + 1);
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_applied_symbols_inner(assumption, VarSort::Bool, declared, found, depth + 1);
            collect_applied_symbols_inner(body, expected, declared, found, depth + 1);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_applied_symbols_inner(obligation, VarSort::Bool, declared, found, depth + 1);
            collect_applied_symbols_inner(body, expected, declared, found, depth + 1);
        }
        PureExpr::Closure { body, .. } => {
            collect_applied_symbols_inner(body, expected, declared, found, depth + 1);
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(..) => {}
    }
}
