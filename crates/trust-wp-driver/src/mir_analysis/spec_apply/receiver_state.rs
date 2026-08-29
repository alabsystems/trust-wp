// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Receiver state advancement and `Final` wrapping for closure environments.
//!
//! Handles stripping/wrapping deref and `Final` nodes to connect
//! postcondition_mut state witnesses to the advanced closure env state.

use trust_wp_core::formula::{internal::tuple_lowering::tuple_logic_fn_arity, PureExpr};

use super::expr_traversal::replace_var_allow_bound;
use crate::callbacks::{final_receiver_state_expr, strip_receiver_state_wrappers};

pub(super) fn connect_final_receiver_state_witness(
    expr: PureExpr,
    self_expr: Option<&PureExpr>,
) -> PureExpr {
    let Some(self_expr) = self_expr else {
        return expr;
    };
    let stripped_self = strip_receiver_state_wrappers(self_expr);
    let is_concrete_closure_env = matches!(
        &stripped_self,
        PureExpr::LogicFnCall { name, args } if tuple_logic_fn_arity(name) == Some(args.len())
    );
    if !is_concrete_closure_env {
        return expr;
    }
    let Some(state_var) = last_postcondition_mut_state_var(&expr) else {
        return expr;
    };

    replace_var_allow_bound(&expr, &state_var, &final_receiver_state_expr(self_expr))
}

fn last_postcondition_mut_state_var(expr: &PureExpr) -> Option<String> {
    fn visit(expr: &PureExpr, last: &mut Option<String>) {
        match expr {
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                visit(receiver, last);
                for arg in args {
                    visit(arg, last);
                }
                if method == "postcondition_mut" && args.len() >= 2 {
                    if let PureExpr::Var(name, _) = &args[args.len() - 2] {
                        *last = Some(name.clone());
                    }
                }
            }
            PureExpr::BinOp(left, _, right) => {
                visit(left, last);
                visit(right, last);
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => {
                visit(inner, last);
            }
            PureExpr::Ite(cond, then_expr, else_expr) => {
                visit(cond, last);
                visit(then_expr, last);
                visit(else_expr, last);
            }
            PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
                for trigger in triggers {
                    for trigger_expr in trigger {
                        visit(trigger_expr, last);
                    }
                }
                visit(body, last);
            }
            PureExpr::Match { scrutinee, arms } => {
                visit(scrutinee, last);
                for arm in arms {
                    visit(&arm.body, last);
                }
            }
            PureExpr::LogicFnCall { args, .. } => {
                for arg in args {
                    visit(arg, last);
                }
            }
            PureExpr::Let { value, body, .. } => {
                visit(value, last);
                visit(body, last);
            }
            PureExpr::LetAssume { assumption, body } => {
                visit(assumption, last);
                visit(body, last);
            }
            PureExpr::LetObligation { obligation, body } => {
                visit(obligation, last);
                visit(body, last);
            }
            PureExpr::Closure { body, .. } => {
                visit(body, last);
            }
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Var(_, _) => {}
            // PureExpr is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns)]
            _ => {}
        }
    }

    let mut last = None;
    visit(expr, &mut last);
    last
}
