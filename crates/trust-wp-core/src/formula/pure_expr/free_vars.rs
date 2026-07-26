// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Binding-aware free-variable analysis for `PureExpr`.
//!
//! All APIs here correctly scope binders from quantifiers, `let` bindings,
//! match-arm patterns, and closure parameters.

use std::collections::HashSet;

use super::{ExprSort, MatchArm, PureExpr};

impl PureExpr {
    /// Collect all free variable names in this expression.
    ///
    /// Correctly excludes bound variables from quantifiers (`forall`, `exists`),
    /// `let` bindings, match arm pattern bindings, and closure parameters.
    /// Uses per-arm scoping for match arms (#484).
    #[must_use]
    pub fn free_vars(&self) -> HashSet<String> {
        let mut vars = HashSet::new();
        Self::collect_free_vars(self, &mut vars);
        vars
    }

    /// Return true if any free variable in this expression satisfies `pred`.
    ///
    /// A variable is "free" if it is not bound by any enclosing `Forall`/`Exists`,
    /// `Let`, match arm pattern, or `Closure` parameter. Binder shadowing is
    /// handled correctly: if an inner binder re-binds the same name, the inner
    /// references are not considered free.
    ///
    /// Uses mutable add/remove on the bound-variable set for O(1) per binder
    /// boundary (no cloning).
    pub fn any_free_var(&self, mut pred: impl FnMut(&str, &Option<ExprSort>) -> bool) -> bool {
        let mut bound = HashSet::new();
        self.any_free_var_impl(&mut pred, &mut bound)
    }

    /// Visit every free variable in this expression.
    ///
    /// Same binding-context tracking as `any_free_var`: quantifier-bound,
    /// let-bound, match-pattern-bound, and closure-parameter-bound names are
    /// excluded. The visitor receives `(name, sort)` references tied to the
    /// expression's lifetime, enabling zero-copy collection.
    pub fn for_each_free_var<'a>(&'a self, mut visit: impl FnMut(&'a str, &'a Option<ExprSort>)) {
        let mut bound = HashSet::new();
        self.for_each_free_var_impl(&mut visit, &mut bound);
    }

    #[allow(clippy::too_many_lines)]
    fn any_free_var_impl<'a, F>(&'a self, pred: &mut F, bound: &mut HashSet<&'a str>) -> bool
    where
        F: FnMut(&str, &Option<ExprSort>) -> bool,
    {
        match self {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => false,
            PureExpr::Var(name, sort) => {
                if bound.contains(name.as_str()) {
                    false
                } else {
                    pred(name.as_str(), sort)
                }
            }
            PureExpr::BinOp(left, _, right) => {
                left.any_free_var_impl(pred, bound) || right.any_free_var_impl(pred, bound)
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => inner.any_free_var_impl(pred, bound),
            PureExpr::Ite(cond, then_expr, else_expr) => {
                cond.any_free_var_impl(pred, bound)
                    || then_expr.any_free_var_impl(pred, bound)
                    || else_expr.any_free_var_impl(pred, bound)
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                receiver.any_free_var_impl(pred, bound)
                    || args.iter().any(|arg| arg.any_free_var_impl(pred, bound))
            }
            PureExpr::LogicFnCall { args, .. } => {
                args.iter().any(|arg| arg.any_free_var_impl(pred, bound))
            }
            PureExpr::Forall {
                var,
                body,
                triggers,
                ..
            }
            | PureExpr::Exists {
                var,
                body,
                triggers,
                ..
            } => {
                let is_new = bound.insert(var.as_str());
                let result = body.any_free_var_impl(pred, bound)
                    || triggers
                        .iter()
                        .flatten()
                        .any(|t| t.any_free_var_impl(pred, bound));
                if is_new {
                    bound.remove(var.as_str());
                }
                result
            }
            PureExpr::Match { scrutinee, arms } => {
                scrutinee.any_free_var_impl(pred, bound)
                    || arms.iter().any(|arm| {
                        let added: Vec<&str> = arm
                            .pattern
                            .bound_names()
                            .into_iter()
                            .filter(|n| bound.insert(n))
                            .collect();
                        let result = arm.body.any_free_var_impl(pred, bound);
                        for n in added {
                            bound.remove(n);
                        }
                        result
                    })
            }
            PureExpr::Let { var, value, body } => {
                if value.any_free_var_impl(pred, bound) {
                    return true;
                }
                let is_new = bound.insert(var.as_str());
                let result = body.any_free_var_impl(pred, bound);
                if is_new {
                    bound.remove(var.as_str());
                }
                result
            }
            PureExpr::LetAssume { assumption, body }
            | PureExpr::LetObligation {
                obligation: assumption,
                body,
            } => assumption.any_free_var_impl(pred, bound) || body.any_free_var_impl(pred, bound),
            PureExpr::Closure { params, body } => {
                let added: Vec<&str> = params
                    .iter()
                    .filter_map(|(p, _)| {
                        if bound.insert(p.as_str()) {
                            Some(p.as_str())
                        } else {
                            None
                        }
                    })
                    .collect();
                let result = body.any_free_var_impl(pred, bound);
                for n in added {
                    bound.remove(n);
                }
                result
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn for_each_free_var_impl<'a, F>(&'a self, visit: &mut F, bound: &mut HashSet<&'a str>)
    where
        F: FnMut(&'a str, &'a Option<ExprSort>),
    {
        match self {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => {}
            PureExpr::Var(name, sort) => {
                if !bound.contains(name.as_str()) {
                    visit(name.as_str(), sort);
                }
            }
            PureExpr::BinOp(left, _, right) => {
                left.for_each_free_var_impl(visit, bound);
                right.for_each_free_var_impl(visit, bound);
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => inner.for_each_free_var_impl(visit, bound),
            PureExpr::Ite(cond, then_expr, else_expr) => {
                cond.for_each_free_var_impl(visit, bound);
                then_expr.for_each_free_var_impl(visit, bound);
                else_expr.for_each_free_var_impl(visit, bound);
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                receiver.for_each_free_var_impl(visit, bound);
                for arg in args {
                    arg.for_each_free_var_impl(visit, bound);
                }
            }
            PureExpr::LogicFnCall { args, .. } => {
                for arg in args {
                    arg.for_each_free_var_impl(visit, bound);
                }
            }
            PureExpr::Forall {
                var,
                body,
                triggers,
                ..
            }
            | PureExpr::Exists {
                var,
                body,
                triggers,
                ..
            } => {
                let is_new = bound.insert(var.as_str());
                body.for_each_free_var_impl(visit, bound);
                for trigger in triggers.iter().flatten() {
                    trigger.for_each_free_var_impl(visit, bound);
                }
                if is_new {
                    bound.remove(var.as_str());
                }
            }
            PureExpr::Match { scrutinee, arms } => {
                scrutinee.for_each_free_var_impl(visit, bound);
                for arm in arms {
                    let added: Vec<&str> = arm
                        .pattern
                        .bound_names()
                        .into_iter()
                        .filter(|n| bound.insert(n))
                        .collect();
                    arm.body.for_each_free_var_impl(visit, bound);
                    for n in added {
                        bound.remove(n);
                    }
                }
            }
            PureExpr::Let { var, value, body } => {
                value.for_each_free_var_impl(visit, bound);
                let is_new = bound.insert(var.as_str());
                body.for_each_free_var_impl(visit, bound);
                if is_new {
                    bound.remove(var.as_str());
                }
            }
            PureExpr::LetAssume { assumption, body }
            | PureExpr::LetObligation {
                obligation: assumption,
                body,
            } => {
                assumption.for_each_free_var_impl(visit, bound);
                body.for_each_free_var_impl(visit, bound);
            }
            PureExpr::Closure { params, body } => {
                let added: Vec<&str> = params
                    .iter()
                    .filter_map(|(p, _)| {
                        if bound.insert(p.as_str()) {
                            Some(p.as_str())
                        } else {
                            None
                        }
                    })
                    .collect();
                body.for_each_free_var_impl(visit, bound);
                for n in added {
                    bound.remove(n);
                }
            }
        }
    }

    fn collect_quantifier_free_vars(
        var: &str,
        body: &PureExpr,
        triggers: &[Vec<PureExpr>],
        vars: &mut HashSet<String>,
    ) {
        let mut scoped_vars = HashSet::new();
        Self::collect_free_vars(body, &mut scoped_vars);
        for trigger in triggers {
            for trigger_expr in trigger {
                Self::collect_free_vars(trigger_expr, &mut scoped_vars);
            }
        }
        scoped_vars.remove(var);
        vars.extend(scoped_vars);
    }

    fn collect_match_free_vars(
        scrutinee: &PureExpr,
        arms: &[MatchArm],
        vars: &mut HashSet<String>,
    ) {
        Self::collect_free_vars(scrutinee, vars);
        for arm in arms {
            let mut arm_vars = HashSet::new();
            Self::collect_free_vars(&arm.body, &mut arm_vars);
            for bound in arm.pattern.bound_names() {
                arm_vars.remove(bound);
            }
            vars.extend(arm_vars);
        }
    }

    fn collect_closure_free_vars(
        params: &[(String, Option<ExprSort>)],
        body: &PureExpr,
        vars: &mut HashSet<String>,
    ) {
        let mut scoped_vars = HashSet::new();
        Self::collect_free_vars(body, &mut scoped_vars);
        for (name, _) in params {
            scoped_vars.remove(name);
        }
        vars.extend(scoped_vars);
    }

    fn collect_free_vars_from_exprs(exprs: &[PureExpr], vars: &mut HashSet<String>) {
        for expr in exprs {
            Self::collect_free_vars(expr, vars);
        }
    }

    fn collect_free_vars(expr: &PureExpr, vars: &mut HashSet<String>) {
        match expr {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => {}
            PureExpr::Var(name, _) => {
                vars.insert(name.clone());
            }
            PureExpr::BinOp(left, _, right) => {
                Self::collect_free_vars(left, vars);
                Self::collect_free_vars(right, vars);
            }
            PureExpr::UnOp(_, operand) => {
                Self::collect_free_vars(operand, vars);
            }
            PureExpr::Ite(cond, then_expr, else_expr) => {
                Self::collect_free_vars(cond, vars);
                Self::collect_free_vars(then_expr, vars);
                Self::collect_free_vars(else_expr, vars);
            }
            PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => {
                Self::collect_free_vars(inner, vars);
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                Self::collect_free_vars(receiver, vars);
                Self::collect_free_vars_from_exprs(args, vars);
            }
            PureExpr::Forall {
                var,
                body,
                triggers,
                ..
            }
            | PureExpr::Exists {
                var,
                body,
                triggers,
                ..
            } => Self::collect_quantifier_free_vars(var, body, triggers, vars),
            PureExpr::Match { scrutinee, arms } => {
                Self::collect_match_free_vars(scrutinee, arms, vars);
            }
            PureExpr::LogicFnCall { args, .. } => Self::collect_free_vars_from_exprs(args, vars),
            PureExpr::Let { var, value, body } => {
                Self::collect_free_vars(value, vars);
                let had_var = vars.contains(var.as_str());
                Self::collect_free_vars(body, vars);
                if !had_var {
                    vars.remove(var);
                }
            }
            PureExpr::LetAssume { assumption, body }
            | PureExpr::LetObligation {
                obligation: assumption,
                body,
            } => {
                Self::collect_free_vars(assumption, vars);
                Self::collect_free_vars(body, vars);
            }
            PureExpr::Closure { params, body } => {
                Self::collect_closure_free_vars(params, body, vars);
            }
        }
    }
}
