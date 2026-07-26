// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Non-binding-aware recursive tree walkers for `PureExpr`.

use super::PureExpr;

impl PureExpr {
    /// Return true if any node in this expression tree matches `pred`.
    pub fn any_recursive(&self, mut pred: impl FnMut(&PureExpr) -> bool) -> bool {
        self.any_recursive_impl(&mut pred)
    }

    /// Visit every node in this expression tree in depth-first pre-order.
    pub fn for_each_recursive(&self, mut visit: impl FnMut(&PureExpr)) {
        self.for_each_recursive_impl(&mut visit);
    }

    fn any_recursive_impl<F>(&self, pred: &mut F) -> bool
    where
        F: FnMut(&PureExpr) -> bool,
    {
        if pred(self) {
            return true;
        }

        match self {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {
                false
            }
            PureExpr::BinOp(left, _, right) => {
                left.any_recursive_impl(pred) || right.any_recursive_impl(pred)
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => inner.any_recursive_impl(pred),
            PureExpr::Ite(cond, then_expr, else_expr) => {
                cond.any_recursive_impl(pred)
                    || then_expr.any_recursive_impl(pred)
                    || else_expr.any_recursive_impl(pred)
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                receiver.any_recursive_impl(pred)
                    || args.iter().any(|arg| arg.any_recursive_impl(pred))
            }
            PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
                body.any_recursive_impl(pred)
                    || triggers
                        .iter()
                        .flat_map(|trigger| trigger.iter())
                        .any(|expr| expr.any_recursive_impl(pred))
            }
            PureExpr::Match { scrutinee, arms } => {
                scrutinee.any_recursive_impl(pred)
                    || arms.iter().any(|arm| arm.body.any_recursive_impl(pred))
            }
            PureExpr::LogicFnCall { args, .. } => {
                args.iter().any(|arg| arg.any_recursive_impl(pred))
            }
            PureExpr::Let { value, body, .. } => {
                value.any_recursive_impl(pred) || body.any_recursive_impl(pred)
            }
            PureExpr::LetAssume { assumption, body } => {
                assumption.any_recursive_impl(pred) || body.any_recursive_impl(pred)
            }
            PureExpr::LetObligation { obligation, body } => {
                obligation.any_recursive_impl(pred) || body.any_recursive_impl(pred)
            }
            PureExpr::Closure { body, .. } => body.any_recursive_impl(pred),
        }
    }

    fn for_each_recursive_impl<F>(&self, visit: &mut F)
    where
        F: FnMut(&PureExpr),
    {
        visit(self);

        match self {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
            PureExpr::BinOp(left, _, right) => {
                left.for_each_recursive_impl(visit);
                right.for_each_recursive_impl(visit);
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => inner.for_each_recursive_impl(visit),
            PureExpr::Ite(cond, then_expr, else_expr) => {
                cond.for_each_recursive_impl(visit);
                then_expr.for_each_recursive_impl(visit);
                else_expr.for_each_recursive_impl(visit);
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                receiver.for_each_recursive_impl(visit);
                for arg in args {
                    arg.for_each_recursive_impl(visit);
                }
            }
            PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
                body.for_each_recursive_impl(visit);
                for trigger in triggers {
                    for expr in trigger {
                        expr.for_each_recursive_impl(visit);
                    }
                }
            }
            PureExpr::Match { scrutinee, arms } => {
                scrutinee.for_each_recursive_impl(visit);
                for arm in arms {
                    arm.body.for_each_recursive_impl(visit);
                }
            }
            PureExpr::LogicFnCall { args, .. } => {
                for arg in args {
                    arg.for_each_recursive_impl(visit);
                }
            }
            PureExpr::Let { value, body, .. } => {
                value.for_each_recursive_impl(visit);
                body.for_each_recursive_impl(visit);
            }
            PureExpr::LetAssume { assumption, body } => {
                assumption.for_each_recursive_impl(visit);
                body.for_each_recursive_impl(visit);
            }
            PureExpr::LetObligation { obligation, body } => {
                obligation.for_each_recursive_impl(visit);
                body.for_each_recursive_impl(visit);
            }
            PureExpr::Closure { body, .. } => body.for_each_recursive_impl(visit),
        }
    }

    // ── Binding-aware walkers ──────────────────────────────────────────

    /// Return true if any node in this expression tree (where `var` is free)
    /// matches `pred`.
    ///
    /// Like `any_recursive`, but skips subtrees where `var` is shadowed by a
    /// binder (`Forall`, `Exists`, `Let`, `Closure` params, `Match` arm
    /// pattern bindings). Quantifier triggers are still visited because they
    /// are outside the binding scope.
    pub fn any_recursive_binding_aware(
        &self,
        var: &str,
        mut pred: impl FnMut(&PureExpr) -> bool,
    ) -> bool {
        self.any_recursive_binding_aware_impl(var, &mut pred)
    }

    /// Visit every node in this expression tree (where `var` is free) in
    /// depth-first pre-order, skipping subtrees where `var` is shadowed.
    pub fn for_each_recursive_binding_aware(&self, var: &str, mut visit: impl FnMut(&PureExpr)) {
        self.for_each_recursive_binding_aware_impl(var, &mut visit);
    }

    fn any_recursive_binding_aware_impl<F>(&self, var: &str, pred: &mut F) -> bool
    where
        F: FnMut(&PureExpr) -> bool,
    {
        if pred(self) {
            return true;
        }

        match self {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {
                false
            }
            PureExpr::BinOp(left, _, right) => {
                left.any_recursive_binding_aware_impl(var, pred)
                    || right.any_recursive_binding_aware_impl(var, pred)
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => inner.any_recursive_binding_aware_impl(var, pred),
            PureExpr::Ite(cond, then_expr, else_expr) => {
                cond.any_recursive_binding_aware_impl(var, pred)
                    || then_expr.any_recursive_binding_aware_impl(var, pred)
                    || else_expr.any_recursive_binding_aware_impl(var, pred)
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                receiver.any_recursive_binding_aware_impl(var, pred)
                    || args
                        .iter()
                        .any(|arg| arg.any_recursive_binding_aware_impl(var, pred))
            }
            PureExpr::Forall {
                var: bound,
                body,
                triggers,
                ..
            }
            | PureExpr::Exists {
                var: bound,
                body,
                triggers,
                ..
            } => {
                // Triggers are outside binding scope — always visit.
                let trigger_hit = triggers
                    .iter()
                    .flat_map(|trigger| trigger.iter())
                    .any(|expr| expr.any_recursive_binding_aware_impl(var, pred));
                if trigger_hit {
                    return true;
                }
                // Body is skipped when `var` is shadowed by the binder.
                bound != var && body.any_recursive_binding_aware_impl(var, pred)
            }
            PureExpr::Match { scrutinee, arms } => {
                scrutinee.any_recursive_binding_aware_impl(var, pred)
                    || arms.iter().any(|arm| {
                        !arm.pattern.binds_name(var)
                            && arm.body.any_recursive_binding_aware_impl(var, pred)
                    })
            }
            PureExpr::LogicFnCall { args, .. } => args
                .iter()
                .any(|arg| arg.any_recursive_binding_aware_impl(var, pred)),
            PureExpr::Let {
                var: bound,
                value,
                body,
            } => {
                value.any_recursive_binding_aware_impl(var, pred)
                    || (bound != var && body.any_recursive_binding_aware_impl(var, pred))
            }
            PureExpr::LetAssume { assumption, body } => {
                assumption.any_recursive_binding_aware_impl(var, pred)
                    || body.any_recursive_binding_aware_impl(var, pred)
            }
            PureExpr::LetObligation { obligation, body } => {
                obligation.any_recursive_binding_aware_impl(var, pred)
                    || body.any_recursive_binding_aware_impl(var, pred)
            }
            PureExpr::Closure { params, body } => {
                !params.iter().any(|(name, _)| name == var)
                    && body.any_recursive_binding_aware_impl(var, pred)
            }
        }
    }

    fn for_each_recursive_binding_aware_impl<F>(&self, var: &str, visit: &mut F)
    where
        F: FnMut(&PureExpr),
    {
        visit(self);

        match self {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
            PureExpr::BinOp(left, _, right) => {
                left.for_each_recursive_binding_aware_impl(var, visit);
                right.for_each_recursive_binding_aware_impl(var, visit);
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => inner.for_each_recursive_binding_aware_impl(var, visit),
            PureExpr::Ite(cond, then_expr, else_expr) => {
                cond.for_each_recursive_binding_aware_impl(var, visit);
                then_expr.for_each_recursive_binding_aware_impl(var, visit);
                else_expr.for_each_recursive_binding_aware_impl(var, visit);
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                receiver.for_each_recursive_binding_aware_impl(var, visit);
                for arg in args {
                    arg.for_each_recursive_binding_aware_impl(var, visit);
                }
            }
            PureExpr::Forall {
                var: bound,
                body,
                triggers,
                ..
            }
            | PureExpr::Exists {
                var: bound,
                body,
                triggers,
                ..
            } => {
                for trigger in triggers {
                    for expr in trigger {
                        expr.for_each_recursive_binding_aware_impl(var, visit);
                    }
                }
                if bound != var {
                    body.for_each_recursive_binding_aware_impl(var, visit);
                }
            }
            PureExpr::Match { scrutinee, arms } => {
                scrutinee.for_each_recursive_binding_aware_impl(var, visit);
                for arm in arms {
                    if !arm.pattern.binds_name(var) {
                        arm.body.for_each_recursive_binding_aware_impl(var, visit);
                    }
                }
            }
            PureExpr::LogicFnCall { args, .. } => {
                for arg in args {
                    arg.for_each_recursive_binding_aware_impl(var, visit);
                }
            }
            PureExpr::Let {
                var: bound,
                value,
                body,
            } => {
                value.for_each_recursive_binding_aware_impl(var, visit);
                if bound != var {
                    body.for_each_recursive_binding_aware_impl(var, visit);
                }
            }
            PureExpr::LetAssume { assumption, body } => {
                assumption.for_each_recursive_binding_aware_impl(var, visit);
                body.for_each_recursive_binding_aware_impl(var, visit);
            }
            PureExpr::LetObligation { obligation, body } => {
                obligation.for_each_recursive_binding_aware_impl(var, visit);
                body.for_each_recursive_binding_aware_impl(var, visit);
            }
            PureExpr::Closure { params, body } => {
                if !params.iter().any(|(name, _)| name == var) {
                    body.for_each_recursive_binding_aware_impl(var, visit);
                }
            }
        }
    }
}
