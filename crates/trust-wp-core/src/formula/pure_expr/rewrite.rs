// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bottom-up rewrite engines for `PureExpr`.
//!
//! All three public rewrite APIs share a single internal rebuild path
//! (`rewrite_inner`), eliminating the previous duplication between
//! prune-only and depth-limited engines.

use std::sync::Arc;

use super::{super::BinOp, reuse_arc, reuse_node, MatchArm, Pattern, PureExpr};

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PureExprChildRole {
    Root,
    MethodReceiver,
    MethodArg,
    LogicFnArg,
    QuantifierBody,
    QuantifierTrigger,
    MatchScrutinee,
    MatchArmBody,
    LetValue,
    LetBody,
    LetAssumeAssumption,
    LetAssumeBody,
    LetObligationObligation,
    LetObligationBody,
    FinalInner,
    OldInner,
    DerefInner,
    ViewInner,
    UnaryOperand,
    BinaryLeft,
    BinaryRight,
    IteCondition,
    IteThen,
    IteElse,
    ClosureBody,
}

impl PureExpr {
    /// Rebuild this expression bottom-up, then apply `rewrite` to each rebuilt node.
    #[must_use]
    pub fn rewrite_bottom_up(&self, mut rewrite: impl FnMut(PureExpr) -> PureExpr) -> PureExpr {
        self.rewrite_inner(0, None, &mut |_| true, &mut rewrite)
    }

    /// Rebuild this expression bottom-up, but skip descending into any node
    /// where `descend` returns `false`.
    ///
    /// The `rewrite` callback still runs on pruned nodes; it just sees the
    /// original subtree instead of a recursively rebuilt one. This lets callers
    /// preserve explicit traversal boundaries while still centralizing the
    /// recursion rules in `PureExpr`.
    #[must_use]
    pub fn rewrite_bottom_up_prune(
        &self,
        mut descend: impl FnMut(&PureExpr) -> bool,
        mut rewrite: impl FnMut(PureExpr) -> PureExpr,
    ) -> PureExpr {
        self.rewrite_inner(0, None, &mut descend, &mut rewrite)
    }

    /// Rebuild this expression bottom-up while both:
    /// - skipping descent into any node where `descend` returns `false`
    /// - preserving any subtree deeper than `depth_limit` unchanged
    ///
    /// As with [`Self::rewrite_bottom_up_prune`], the `rewrite` callback still
    /// runs on pruned nodes; it does not run on nodes beyond `depth_limit`.
    #[must_use]
    pub fn rewrite_bottom_up_prune_with_depth_limit(
        &self,
        depth_limit: usize,
        mut descend: impl FnMut(&PureExpr) -> bool,
        mut rewrite: impl FnMut(PureExpr) -> PureExpr,
    ) -> PureExpr {
        self.rewrite_inner(0, Some(depth_limit), &mut descend, &mut rewrite)
    }

    /// Rebuild this expression bottom-up while both:
    /// - skipping descent into any node where `descend` returns `false`
    /// - preserving any subtree deeper than `depth_limit` unchanged
    ///
    /// The `rewrite` callback returns `Some(new_node)` only when it changes the
    /// rebuilt node; returning `None` keeps the existing node unchanged.
    ///
    /// Returns `Some(new_expr)` when any descendant or the current node
    /// changes, otherwise `None`.
    #[must_use]
    pub fn rewrite_bottom_up_prune_with_depth_limit_if_changed(
        &self,
        depth_limit: usize,
        mut descend: impl FnMut(&PureExpr) -> bool,
        mut rewrite: impl FnMut(PureExpr) -> Option<PureExpr>,
    ) -> Option<PureExpr> {
        self.rewrite_inner_if_changed(0, Some(depth_limit), &mut descend, &mut rewrite)
    }

    /// Rebuild this expression bottom-up while attaching caller-defined state
    /// to each node based on its parent edge role.
    #[must_use]
    pub fn rewrite_bottom_up_with_context<S: Clone>(
        &self,
        initial_state: S,
        mut descend: impl FnMut(&S, PureExprChildRole, &PureExpr) -> S,
        mut rewrite: impl FnMut(PureExpr, &S) -> PureExpr,
    ) -> PureExpr {
        self.rewrite_inner_with_context(&initial_state, &mut descend, &mut rewrite)
    }

    /// Collapse *identity* `match`/`if`-chains to their scrutinee.
    ///
    /// An expression is an identity over `s` when it provably evaluates to `s`
    /// for every value of `s`. Two shapes are recognized:
    ///
    /// 1. **`match s { lit => lit, …, _ => s }`** — every literal arm returns
    ///    its own matched literal (which equals `s` in that arm) and an
    ///    exhaustive catch-all (`_ => s` or `name => name`) returns the
    ///    scrutinee.
    /// 2. **`Ite(s == c, c, …else…)`** bottoming at `else == s` — the lowered
    ///    form the driver actually emits for an integer match (SwitchInt →
    ///    nested `Ite`): `match x { -1 => -1, 127 => 127, _ => x }` becomes
    ///    `Ite(x==-1, -1, Ite(x==127, 127, x))`.
    ///
    /// Lowering such an identity to an SMT discriminant case-split is correct
    /// but quadratic: each independent body match adds an arm-selection split
    /// and the solver explores their product (a function with 4 sequential
    /// identity matches times out vs ~0s for one — see `bug/negative_int_pats`).
    /// Collapsing to the scrutinee removes the split entirely.
    ///
    /// SOUNDNESS: an identity match/`Ite`-chain equals its scrutinee on every
    /// input, so the rewrite is a semantics-preserving substitution. The checks
    /// are deliberately conservative (exhaustive catch-all returning the
    /// scrutinee; each `Ite` condition is `scrutinee == <constant>` with the
    /// then-branch that same constant) so they can never change meaning.
    #[must_use]
    pub fn simplify_identity_matches(&self) -> PureExpr {
        self.rewrite_bottom_up(|node| match &node {
            PureExpr::Match { scrutinee, arms } if is_identity_match(scrutinee, arms) => {
                (**scrutinee).clone()
            }
            PureExpr::Ite(..) => match ite_identity_scrutinee(&node) {
                Some(scrutinee) => scrutinee.clone(),
                None => node,
            },
            // Tautology cleanup so the collapse above can cascade: once an
            // identity binding `y == match x { .. => x }` becomes `y == x` and the
            // proof goal `x == y` is substituted to `call == call`, reduce it to a
            // literal `true` that the proof_assert verifier discharges WITHOUT the
            // solver. SOUND: `a == a` holds for every value (trust-wp models Float
            // as SMT Real — no NaN), and the `&&`/`||` cases are standard boolean
            // identities.
            PureExpr::BinOp(l, op, r) => {
                let reduced = match op {
                    BinOp::Eq if l == r => Some(PureExpr::Bool(true)),
                    BinOp::And => match (l.as_ref(), r.as_ref()) {
                        (PureExpr::Bool(true), _) => Some((**r).clone()),
                        (_, PureExpr::Bool(true)) => Some((**l).clone()),
                        (PureExpr::Bool(false), _) | (_, PureExpr::Bool(false)) => {
                            Some(PureExpr::Bool(false))
                        }
                        _ => None,
                    },
                    BinOp::Or => match (l.as_ref(), r.as_ref()) {
                        (PureExpr::Bool(true), _) | (_, PureExpr::Bool(true)) => {
                            Some(PureExpr::Bool(true))
                        }
                        (PureExpr::Bool(false), _) => Some((**r).clone()),
                        (_, PureExpr::Bool(false)) => Some((**l).clone()),
                        _ => None,
                    },
                    _ => None,
                };
                reduced.unwrap_or(node)
            }
            _ => node,
        })
    }

    #[allow(clippy::too_many_lines)]
    fn rewrite_inner<D, F>(
        &self,
        depth: usize,
        depth_limit: Option<usize>,
        descend: &mut D,
        rewrite: &mut F,
    ) -> PureExpr
    where
        D: FnMut(&PureExpr) -> bool,
        F: FnMut(PureExpr) -> PureExpr,
    {
        if depth_limit.is_some_and(|limit| depth > limit) {
            return self.clone();
        }

        if !descend(self) {
            return reuse_node(self, rewrite(self.clone()));
        }

        let next = depth + 1;
        let rebuilt = match self {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {
                self.clone()
            }
            PureExpr::BinOp(left, op, right) => {
                let new_left = left.rewrite_inner(next, depth_limit, descend, rewrite);
                let new_right = right.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::BinOp(reuse_arc(left, new_left), *op, reuse_arc(right, new_right)),
                )
            }
            PureExpr::UnOp(op, inner) => {
                let new_inner = inner.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(self, PureExpr::UnOp(*op, reuse_arc(inner, new_inner)))
            }
            PureExpr::Ite(cond, then_expr, else_expr) => {
                let new_cond = cond.rewrite_inner(next, depth_limit, descend, rewrite);
                let new_then = then_expr.rewrite_inner(next, depth_limit, descend, rewrite);
                let new_else = else_expr.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::Ite(
                        reuse_arc(cond, new_cond),
                        reuse_arc(then_expr, new_then),
                        reuse_arc(else_expr, new_else),
                    ),
                )
            }
            PureExpr::Old(inner) => {
                let new_inner = inner.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(self, PureExpr::Old(reuse_arc(inner, new_inner)))
            }
            PureExpr::Deref(inner) => {
                let new_inner = inner.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(self, PureExpr::Deref(reuse_arc(inner, new_inner)))
            }
            PureExpr::Final(inner) => {
                let new_inner = inner.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(self, PureExpr::Final(reuse_arc(inner, new_inner)))
            }
            PureExpr::View(inner) => {
                let new_inner = inner.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(self, PureExpr::View(reuse_arc(inner, new_inner)))
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let new_receiver = receiver.rewrite_inner(next, depth_limit, descend, rewrite);
                let new_args = args
                    .iter()
                    .map(|arg| arg.rewrite_inner(next, depth_limit, descend, rewrite))
                    .collect();
                reuse_node(
                    self,
                    PureExpr::MethodCall {
                        receiver: reuse_arc(receiver, new_receiver),
                        method: method.clone(),
                        args: new_args,
                    },
                )
            }
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let new_body = body.rewrite_inner(next, depth_limit, descend, rewrite);
                let new_triggers = triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| expr.rewrite_inner(next, depth_limit, descend, rewrite))
                            .collect()
                    })
                    .collect();
                reuse_node(
                    self,
                    PureExpr::Forall {
                        var: var.clone(),
                        var_sort: var_sort.clone(),
                        body: reuse_arc(body, new_body),
                        triggers: new_triggers,
                    },
                )
            }
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let new_body = body.rewrite_inner(next, depth_limit, descend, rewrite);
                let new_triggers = triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| expr.rewrite_inner(next, depth_limit, descend, rewrite))
                            .collect()
                    })
                    .collect();
                reuse_node(
                    self,
                    PureExpr::Exists {
                        var: var.clone(),
                        var_sort: var_sort.clone(),
                        body: reuse_arc(body, new_body),
                        triggers: new_triggers,
                    },
                )
            }
            PureExpr::Match { scrutinee, arms } => {
                let new_scrutinee = scrutinee.rewrite_inner(next, depth_limit, descend, rewrite);
                let new_arms = arms
                    .iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern.clone(),
                        body: arm.body.rewrite_inner(next, depth_limit, descend, rewrite),
                    })
                    .collect();
                reuse_node(
                    self,
                    PureExpr::Match {
                        scrutinee: reuse_arc(scrutinee, new_scrutinee),
                        arms: new_arms,
                    },
                )
            }
            PureExpr::LogicFnCall { name, args } => {
                let new_args = args
                    .iter()
                    .map(|arg| arg.rewrite_inner(next, depth_limit, descend, rewrite))
                    .collect();
                reuse_node(
                    self,
                    PureExpr::LogicFnCall {
                        name: name.clone(),
                        args: new_args,
                    },
                )
            }
            PureExpr::Let { var, value, body } => {
                let new_value = value.rewrite_inner(next, depth_limit, descend, rewrite);
                let new_body = body.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::Let {
                        var: var.clone(),
                        value: reuse_arc(value, new_value),
                        body: reuse_arc(body, new_body),
                    },
                )
            }
            PureExpr::LetAssume { assumption, body } => {
                let new_assumption = assumption.rewrite_inner(next, depth_limit, descend, rewrite);
                let new_body = body.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::LetAssume {
                        assumption: reuse_arc(assumption, new_assumption),
                        body: reuse_arc(body, new_body),
                    },
                )
            }
            PureExpr::LetObligation { obligation, body } => {
                let new_obligation = obligation.rewrite_inner(next, depth_limit, descend, rewrite);
                let new_body = body.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::LetObligation {
                        obligation: reuse_arc(obligation, new_obligation),
                        body: reuse_arc(body, new_body),
                    },
                )
            }
            PureExpr::Closure { params, body } => {
                let new_body = body.rewrite_inner(next, depth_limit, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::Closure {
                        params: params.clone(),
                        body: reuse_arc(body, new_body),
                    },
                )
            }
        };

        reuse_node(self, rewrite(rebuilt))
    }

    #[allow(clippy::too_many_lines)]
    fn rewrite_inner_if_changed<D, F>(
        &self,
        depth: usize,
        depth_limit: Option<usize>,
        descend: &mut D,
        rewrite: &mut F,
    ) -> Option<PureExpr>
    where
        D: FnMut(&PureExpr) -> bool,
        F: FnMut(PureExpr) -> Option<PureExpr>,
    {
        if depth_limit.is_some_and(|limit| depth > limit) {
            return None;
        }

        if !descend(self) {
            return rewrite(self.clone());
        }

        let next = depth + 1;
        let rebuilt = match self {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => None,
            PureExpr::BinOp(left, op, right) => {
                let new_left = left.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                let new_right = right.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                if new_left.is_none() && new_right.is_none() {
                    None
                } else {
                    Some(PureExpr::BinOp(
                        new_left.map_or_else(|| Arc::clone(left), Arc::new),
                        *op,
                        new_right.map_or_else(|| Arc::clone(right), Arc::new),
                    ))
                }
            }
            PureExpr::UnOp(op, inner) => inner
                .rewrite_inner_if_changed(next, depth_limit, descend, rewrite)
                .map(|new_inner| PureExpr::UnOp(*op, Arc::new(new_inner))),
            PureExpr::Ite(cond, then_expr, else_expr) => {
                let new_cond = cond.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                let new_then =
                    then_expr.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                let new_else =
                    else_expr.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                if new_cond.is_none() && new_then.is_none() && new_else.is_none() {
                    None
                } else {
                    Some(PureExpr::Ite(
                        new_cond.map_or_else(|| Arc::clone(cond), Arc::new),
                        new_then.map_or_else(|| Arc::clone(then_expr), Arc::new),
                        new_else.map_or_else(|| Arc::clone(else_expr), Arc::new),
                    ))
                }
            }
            PureExpr::Old(inner) => inner
                .rewrite_inner_if_changed(next, depth_limit, descend, rewrite)
                .map(|new_inner| PureExpr::Old(Arc::new(new_inner))),
            PureExpr::Deref(inner) => inner
                .rewrite_inner_if_changed(next, depth_limit, descend, rewrite)
                .map(|new_inner| PureExpr::Deref(Arc::new(new_inner))),
            PureExpr::Final(inner) => inner
                .rewrite_inner_if_changed(next, depth_limit, descend, rewrite)
                .map(|new_inner| PureExpr::Final(Arc::new(new_inner))),
            PureExpr::View(inner) => inner
                .rewrite_inner_if_changed(next, depth_limit, descend, rewrite)
                .map(|new_inner| PureExpr::View(Arc::new(new_inner))),
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let new_receiver =
                    receiver.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                let new_args: Vec<_> = args
                    .iter()
                    .map(|arg| arg.rewrite_inner_if_changed(next, depth_limit, descend, rewrite))
                    .collect();
                if new_receiver.is_none() && new_args.iter().all(Option::is_none) {
                    None
                } else {
                    Some(PureExpr::MethodCall {
                        receiver: new_receiver.map_or_else(|| Arc::clone(receiver), Arc::new),
                        method: method.clone(),
                        args: args
                            .iter()
                            .zip(new_args)
                            .map(|(arg, maybe_new)| maybe_new.unwrap_or_else(|| arg.clone()))
                            .collect(),
                    })
                }
            }
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let new_body = body.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                let new_triggers: Vec<Vec<Option<PureExpr>>> = triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| {
                                expr.rewrite_inner_if_changed(next, depth_limit, descend, rewrite)
                            })
                            .collect()
                    })
                    .collect();
                let triggers_changed = new_triggers
                    .iter()
                    .flat_map(|trigger| trigger.iter())
                    .any(Option::is_some);
                if new_body.is_none() && !triggers_changed {
                    None
                } else {
                    Some(PureExpr::Forall {
                        var: var.clone(),
                        var_sort: var_sort.clone(),
                        body: new_body.map_or_else(|| Arc::clone(body), Arc::new),
                        triggers: triggers
                            .iter()
                            .zip(new_triggers)
                            .map(|(trigger, new_trigger)| {
                                trigger
                                    .iter()
                                    .zip(new_trigger)
                                    .map(|(expr, maybe_new)| {
                                        maybe_new.unwrap_or_else(|| expr.clone())
                                    })
                                    .collect()
                            })
                            .collect(),
                    })
                }
            }
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let new_body = body.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                let new_triggers: Vec<Vec<Option<PureExpr>>> = triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| {
                                expr.rewrite_inner_if_changed(next, depth_limit, descend, rewrite)
                            })
                            .collect()
                    })
                    .collect();
                let triggers_changed = new_triggers
                    .iter()
                    .flat_map(|trigger| trigger.iter())
                    .any(Option::is_some);
                if new_body.is_none() && !triggers_changed {
                    None
                } else {
                    Some(PureExpr::Exists {
                        var: var.clone(),
                        var_sort: var_sort.clone(),
                        body: new_body.map_or_else(|| Arc::clone(body), Arc::new),
                        triggers: triggers
                            .iter()
                            .zip(new_triggers)
                            .map(|(trigger, new_trigger)| {
                                trigger
                                    .iter()
                                    .zip(new_trigger)
                                    .map(|(expr, maybe_new)| {
                                        maybe_new.unwrap_or_else(|| expr.clone())
                                    })
                                    .collect()
                            })
                            .collect(),
                    })
                }
            }
            PureExpr::Match { scrutinee, arms } => {
                let new_scrutinee =
                    scrutinee.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                let new_arms: Vec<_> = arms
                    .iter()
                    .map(|arm| {
                        arm.body
                            .rewrite_inner_if_changed(next, depth_limit, descend, rewrite)
                    })
                    .collect();
                if new_scrutinee.is_none() && new_arms.iter().all(Option::is_none) {
                    None
                } else {
                    Some(PureExpr::Match {
                        scrutinee: new_scrutinee.map_or_else(|| Arc::clone(scrutinee), Arc::new),
                        arms: arms
                            .iter()
                            .zip(new_arms)
                            .map(|(arm, maybe_new_body)| MatchArm {
                                pattern: arm.pattern.clone(),
                                body: maybe_new_body.unwrap_or_else(|| arm.body.clone()),
                            })
                            .collect(),
                    })
                }
            }
            PureExpr::LogicFnCall { name, args } => {
                let new_args: Vec<_> = args
                    .iter()
                    .map(|arg| arg.rewrite_inner_if_changed(next, depth_limit, descend, rewrite))
                    .collect();
                if new_args.iter().all(Option::is_none) {
                    None
                } else {
                    Some(PureExpr::LogicFnCall {
                        name: name.clone(),
                        args: args
                            .iter()
                            .zip(new_args)
                            .map(|(arg, maybe_new)| maybe_new.unwrap_or_else(|| arg.clone()))
                            .collect(),
                    })
                }
            }
            PureExpr::Let { var, value, body } => {
                let new_value = value.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                let new_body = body.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                if new_value.is_none() && new_body.is_none() {
                    None
                } else {
                    Some(PureExpr::Let {
                        var: var.clone(),
                        value: new_value.map_or_else(|| Arc::clone(value), Arc::new),
                        body: new_body.map_or_else(|| Arc::clone(body), Arc::new),
                    })
                }
            }
            PureExpr::LetAssume { assumption, body } => {
                let new_assumption =
                    assumption.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                let new_body = body.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                if new_assumption.is_none() && new_body.is_none() {
                    None
                } else {
                    Some(PureExpr::LetAssume {
                        assumption: new_assumption.map_or_else(|| Arc::clone(assumption), Arc::new),
                        body: new_body.map_or_else(|| Arc::clone(body), Arc::new),
                    })
                }
            }
            PureExpr::LetObligation { obligation, body } => {
                let new_obligation =
                    obligation.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                let new_body = body.rewrite_inner_if_changed(next, depth_limit, descend, rewrite);
                if new_obligation.is_none() && new_body.is_none() {
                    None
                } else {
                    Some(PureExpr::LetObligation {
                        obligation: new_obligation.map_or_else(|| Arc::clone(obligation), Arc::new),
                        body: new_body.map_or_else(|| Arc::clone(body), Arc::new),
                    })
                }
            }
            PureExpr::Closure { params, body } => body
                .rewrite_inner_if_changed(next, depth_limit, descend, rewrite)
                .map(|new_body| PureExpr::Closure {
                    params: params.clone(),
                    body: Arc::new(new_body),
                }),
        };

        match rebuilt {
            Some(rebuilt) => rewrite(rebuilt.clone()).or(Some(rebuilt)),
            None => rewrite(self.clone()),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn rewrite_inner_with_context<S: Clone, D, F>(
        &self,
        state: &S,
        descend: &mut D,
        rewrite: &mut F,
    ) -> PureExpr
    where
        D: FnMut(&S, PureExprChildRole, &PureExpr) -> S,
        F: FnMut(PureExpr, &S) -> PureExpr,
    {
        let rebuilt = match self {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {
                self.clone()
            }
            PureExpr::BinOp(left, op, right) => {
                let left_state = descend(state, PureExprChildRole::BinaryLeft, left);
                let right_state = descend(state, PureExprChildRole::BinaryRight, right);
                let new_left = left.rewrite_inner_with_context(&left_state, descend, rewrite);
                let new_right = right.rewrite_inner_with_context(&right_state, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::BinOp(reuse_arc(left, new_left), *op, reuse_arc(right, new_right)),
                )
            }
            PureExpr::UnOp(op, inner) => {
                let inner_state = descend(state, PureExprChildRole::UnaryOperand, inner);
                let new_inner = inner.rewrite_inner_with_context(&inner_state, descend, rewrite);
                reuse_node(self, PureExpr::UnOp(*op, reuse_arc(inner, new_inner)))
            }
            PureExpr::Ite(cond, then_expr, else_expr) => {
                let cond_state = descend(state, PureExprChildRole::IteCondition, cond);
                let then_state = descend(state, PureExprChildRole::IteThen, then_expr);
                let else_state = descend(state, PureExprChildRole::IteElse, else_expr);
                let new_cond = cond.rewrite_inner_with_context(&cond_state, descend, rewrite);
                let new_then = then_expr.rewrite_inner_with_context(&then_state, descend, rewrite);
                let new_else = else_expr.rewrite_inner_with_context(&else_state, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::Ite(
                        reuse_arc(cond, new_cond),
                        reuse_arc(then_expr, new_then),
                        reuse_arc(else_expr, new_else),
                    ),
                )
            }
            PureExpr::Old(inner) => {
                let inner_state = descend(state, PureExprChildRole::OldInner, inner);
                let new_inner = inner.rewrite_inner_with_context(&inner_state, descend, rewrite);
                reuse_node(self, PureExpr::Old(reuse_arc(inner, new_inner)))
            }
            PureExpr::Deref(inner) => {
                let inner_state = descend(state, PureExprChildRole::DerefInner, inner);
                let new_inner = inner.rewrite_inner_with_context(&inner_state, descend, rewrite);
                reuse_node(self, PureExpr::Deref(reuse_arc(inner, new_inner)))
            }
            PureExpr::Final(inner) => {
                let inner_state = descend(state, PureExprChildRole::FinalInner, inner);
                let new_inner = inner.rewrite_inner_with_context(&inner_state, descend, rewrite);
                reuse_node(self, PureExpr::Final(reuse_arc(inner, new_inner)))
            }
            PureExpr::View(inner) => {
                let inner_state = descend(state, PureExprChildRole::ViewInner, inner);
                let new_inner = inner.rewrite_inner_with_context(&inner_state, descend, rewrite);
                reuse_node(self, PureExpr::View(reuse_arc(inner, new_inner)))
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let receiver_state = descend(state, PureExprChildRole::MethodReceiver, receiver);
                let new_receiver =
                    receiver.rewrite_inner_with_context(&receiver_state, descend, rewrite);
                let new_args = args
                    .iter()
                    .map(|arg| {
                        let arg_state = descend(state, PureExprChildRole::MethodArg, arg);
                        arg.rewrite_inner_with_context(&arg_state, descend, rewrite)
                    })
                    .collect();
                reuse_node(
                    self,
                    PureExpr::MethodCall {
                        receiver: reuse_arc(receiver, new_receiver),
                        method: method.clone(),
                        args: new_args,
                    },
                )
            }
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let body_state = descend(state, PureExprChildRole::QuantifierBody, body);
                let new_body = body.rewrite_inner_with_context(&body_state, descend, rewrite);
                let new_triggers = triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| {
                                let expr_state =
                                    descend(state, PureExprChildRole::QuantifierTrigger, expr);
                                expr.rewrite_inner_with_context(&expr_state, descend, rewrite)
                            })
                            .collect()
                    })
                    .collect();
                reuse_node(
                    self,
                    PureExpr::Forall {
                        var: var.clone(),
                        var_sort: var_sort.clone(),
                        body: reuse_arc(body, new_body),
                        triggers: new_triggers,
                    },
                )
            }
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let body_state = descend(state, PureExprChildRole::QuantifierBody, body);
                let new_body = body.rewrite_inner_with_context(&body_state, descend, rewrite);
                let new_triggers = triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| {
                                let expr_state =
                                    descend(state, PureExprChildRole::QuantifierTrigger, expr);
                                expr.rewrite_inner_with_context(&expr_state, descend, rewrite)
                            })
                            .collect()
                    })
                    .collect();
                reuse_node(
                    self,
                    PureExpr::Exists {
                        var: var.clone(),
                        var_sort: var_sort.clone(),
                        body: reuse_arc(body, new_body),
                        triggers: new_triggers,
                    },
                )
            }
            PureExpr::Match { scrutinee, arms } => {
                let scrutinee_state = descend(state, PureExprChildRole::MatchScrutinee, scrutinee);
                let new_scrutinee =
                    scrutinee.rewrite_inner_with_context(&scrutinee_state, descend, rewrite);
                let new_arms = arms
                    .iter()
                    .map(|arm| {
                        let body_state = descend(state, PureExprChildRole::MatchArmBody, &arm.body);
                        MatchArm {
                            pattern: arm.pattern.clone(),
                            body: arm.body.rewrite_inner_with_context(
                                &body_state,
                                descend,
                                rewrite,
                            ),
                        }
                    })
                    .collect();
                reuse_node(
                    self,
                    PureExpr::Match {
                        scrutinee: reuse_arc(scrutinee, new_scrutinee),
                        arms: new_arms,
                    },
                )
            }
            PureExpr::LogicFnCall { name, args } => {
                let new_args = args
                    .iter()
                    .map(|arg| {
                        let arg_state = descend(state, PureExprChildRole::LogicFnArg, arg);
                        arg.rewrite_inner_with_context(&arg_state, descend, rewrite)
                    })
                    .collect();
                reuse_node(
                    self,
                    PureExpr::LogicFnCall {
                        name: name.clone(),
                        args: new_args,
                    },
                )
            }
            PureExpr::Let { var, value, body } => {
                let value_state = descend(state, PureExprChildRole::LetValue, value);
                let body_state = descend(state, PureExprChildRole::LetBody, body);
                let new_value = value.rewrite_inner_with_context(&value_state, descend, rewrite);
                let new_body = body.rewrite_inner_with_context(&body_state, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::Let {
                        var: var.clone(),
                        value: reuse_arc(value, new_value),
                        body: reuse_arc(body, new_body),
                    },
                )
            }
            PureExpr::LetAssume { assumption, body } => {
                let assumption_state =
                    descend(state, PureExprChildRole::LetAssumeAssumption, assumption);
                let body_state = descend(state, PureExprChildRole::LetAssumeBody, body);
                let new_assumption =
                    assumption.rewrite_inner_with_context(&assumption_state, descend, rewrite);
                let new_body = body.rewrite_inner_with_context(&body_state, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::LetAssume {
                        assumption: reuse_arc(assumption, new_assumption),
                        body: reuse_arc(body, new_body),
                    },
                )
            }
            PureExpr::LetObligation { obligation, body } => {
                let obligation_state = descend(
                    state,
                    PureExprChildRole::LetObligationObligation,
                    obligation,
                );
                let body_state = descend(state, PureExprChildRole::LetObligationBody, body);
                let new_obligation =
                    obligation.rewrite_inner_with_context(&obligation_state, descend, rewrite);
                let new_body = body.rewrite_inner_with_context(&body_state, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::LetObligation {
                        obligation: reuse_arc(obligation, new_obligation),
                        body: reuse_arc(body, new_body),
                    },
                )
            }
            PureExpr::Closure { params, body } => {
                let body_state = descend(state, PureExprChildRole::ClosureBody, body);
                let new_body = body.rewrite_inner_with_context(&body_state, descend, rewrite);
                reuse_node(
                    self,
                    PureExpr::Closure {
                        params: params.clone(),
                        body: reuse_arc(body, new_body),
                    },
                )
            }
        };

        reuse_node(self, rewrite(rebuilt, state))
    }
}

/// Whether `match scrutinee { arms }` provably equals `scrutinee` for every input.
///
/// Requires (all must hold; otherwise returns `false` and the match is left
/// intact): a non-empty arm list; every `Literal(lit)` arm has a body
/// structurally equal to `lit` (the arm fires only when `scrutinee == lit`, so
/// returning `lit` returns the scrutinee); and an exhaustive catch-all
/// (`Wildcard` with body == `scrutinee`, or `Binding(name)` with body
/// `Var(name)`) that returns the scrutinee. Constructor / tuple / alias
/// patterns, or any other body shape, make this return `false`.
fn is_identity_match(scrutinee: &PureExpr, arms: &[MatchArm]) -> bool {
    if arms.is_empty() {
        return false;
    }
    let mut has_catch_all = false;
    for arm in arms {
        match &arm.pattern {
            Pattern::Literal(lit) => {
                if arm.body != *lit {
                    return false;
                }
            }
            Pattern::Wildcard => {
                if arm.body != *scrutinee {
                    return false;
                }
                has_catch_all = true;
            }
            Pattern::Binding(name) => match &arm.body {
                PureExpr::Var(bound, _) if bound == name => has_catch_all = true,
                _ => return false,
            },
            _ => return false,
        }
    }
    has_catch_all
}

/// A constant literal (`Int`/`Bool`/`Float`) — the only RHS a switch-discriminant
/// equality compares against.
fn is_literal_const(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_)
    )
}

/// If `expr` is an identity `Ite`-chain over some scrutinee `s` — i.e. it
/// provably evaluates to `s` for every value of `s` — return `Some(s)`.
///
/// Shape: `Ite(s == c, c, else)` where `c` is a constant, the then-branch is
/// exactly that constant `c`, and `else` is either `s` itself or, recursively,
/// another identity `Ite`-chain over the SAME `s`. When `s == c` the branch
/// yields `c == s`; otherwise it yields `else`, which (by induction) yields `s`.
/// The final `else == s` is the exhaustive catch-all that makes the chain total.
fn ite_identity_scrutinee(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::Ite(cond, then_br, else_br) = expr else {
        return None;
    };
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = cond.as_ref() else {
        return None;
    };
    // The condition is `s == c`; the constant may be on either side.
    let (scrutinee, constant): (&PureExpr, &PureExpr) = if is_literal_const(rhs) {
        (lhs.as_ref(), rhs.as_ref())
    } else if is_literal_const(lhs) {
        (rhs.as_ref(), lhs.as_ref())
    } else {
        return None;
    };
    // The arm taken when `s == c` must return that same constant `c`.
    if then_br.as_ref() != constant {
        return None;
    }
    // The fall-through must be the scrutinee, or an identity chain over the same scrutinee.
    if else_br.as_ref() == scrutinee {
        return Some(scrutinee);
    }
    match ite_identity_scrutinee(else_br) {
        Some(inner) if inner == scrutinee => Some(scrutinee),
        _ => None,
    }
}

#[cfg(test)]
mod identity_match_tests {
    use super::*;

    fn lit(n: i64) -> PureExpr {
        PureExpr::Int(n)
    }

    #[test]
    fn collapses_integer_identity_match_with_wildcard() {
        // match x { -1 => -1, 127 => 127, _ => x }  ==>  x
        let scrut = PureExpr::Var("x".into(), None);
        let expr = PureExpr::Match {
            scrutinee: Arc::new(scrut.clone()),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(lit(-1)),
                    body: lit(-1),
                },
                MatchArm {
                    pattern: Pattern::Literal(lit(127)),
                    body: lit(127),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: scrut.clone(),
                },
            ],
        };
        assert_eq!(expr.simplify_identity_matches(), scrut);
    }

    #[test]
    fn keeps_non_identity_match() {
        // match x { 0 => 1, _ => x }  is NOT an identity (arm 0 returns 1, not 0)
        let scrut = PureExpr::Var("x".into(), None);
        let expr = PureExpr::Match {
            scrutinee: Arc::new(scrut.clone()),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(lit(0)),
                    body: lit(1),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: scrut.clone(),
                },
            ],
        };
        assert_eq!(expr.simplify_identity_matches(), expr);
    }

    #[test]
    fn keeps_match_without_exhaustive_catch_all() {
        // match x { -1 => -1, 127 => 127 }  has no catch-all => not provably total
        let scrut = PureExpr::Var("x".into(), None);
        let expr = PureExpr::Match {
            scrutinee: Arc::new(scrut.clone()),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(lit(-1)),
                    body: lit(-1),
                },
                MatchArm {
                    pattern: Pattern::Literal(lit(127)),
                    body: lit(127),
                },
            ],
        };
        assert_eq!(expr.simplify_identity_matches(), expr);
    }

    fn eq(l: PureExpr, r: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(l), super::super::BinOp::Eq, Arc::new(r))
    }
    fn ite(c: PureExpr, t: PureExpr, e: PureExpr) -> PureExpr {
        PureExpr::Ite(Arc::new(c), Arc::new(t), Arc::new(e))
    }

    #[test]
    fn collapses_identity_ite_chain_to_scrutinee() {
        // The actual lowered negative_int_pats body binding:
        //   y == Ite(s==-1, -1, Ite(s==-128, -128, Ite(s==127, 127, s)))   ==>  y == s
        let s = PureExpr::Var("call_1".into(), Some(crate::formula::ExprSort::Int));
        let chain = ite(
            eq(s.clone(), lit(-1)),
            lit(-1),
            ite(
                eq(s.clone(), lit(-128)),
                lit(-128),
                ite(eq(s.clone(), lit(127)), lit(127), s.clone()),
            ),
        );
        assert_eq!(chain.simplify_identity_matches(), s);
        // inside an equality, recursing through the BinOp
        let y = PureExpr::Var("y".into(), Some(crate::formula::ExprSort::Int));
        assert_eq!(eq(y.clone(), chain).simplify_identity_matches(), eq(y, s));
    }

    #[test]
    fn keeps_non_identity_ite_chain() {
        // Ite(s==0, 1, s) is NOT identity (then-branch 1 != matched constant 0)
        let s = PureExpr::Var("s".into(), None);
        let chain = ite(eq(s.clone(), lit(0)), lit(1), s.clone());
        assert_eq!(chain.simplify_identity_matches(), chain);
        // Ite(s==0, 0, t) with a different tail var t is NOT identity over s
        let t = PureExpr::Var("t".into(), None);
        let chain2 = ite(eq(s.clone(), lit(0)), lit(0), t);
        assert_eq!(chain2.simplify_identity_matches(), chain2);
    }

    #[test]
    fn collapses_nested_in_equality_and_recurses() {
        // y == match x { -1 => -1, _ => x }  ==>  y == x
        let x = PureExpr::Var("x".into(), None);
        let y = PureExpr::Var("y".into(), None);
        let m = PureExpr::Match {
            scrutinee: Arc::new(x.clone()),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(lit(-1)),
                    body: lit(-1),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: x.clone(),
                },
            ],
        };
        let eq = PureExpr::BinOp(Arc::new(y.clone()), super::super::BinOp::Eq, Arc::new(m));
        let expected = PureExpr::BinOp(Arc::new(y), super::super::BinOp::Eq, Arc::new(x));
        assert_eq!(eq.simplify_identity_matches(), expected);
    }
}
