// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Elaboration: what each subterm of a clause denotes, decided once.
//!
//! Every parse entry point runs [`resolve_aliases`] on the finished clause,
//! so no consumer meets a binder that merely renames a value or a projection
//! of a branch. A lane that knows a contract's parameters reads each
//! parameter's state through `state` ([`place_parameter_reads`],
//! [`postcondition_states`]), and a call reads its callee's clauses through
//! the same functions over the callee's [`Signature`]
//! ([`postcondition_at_a_call`]), so the lane that proves a clause and the
//! call credited with it read it alike. A bundle claim and its native replay
//! read every subterm's sort from [`elaborate`], one unification over the
//! whole claim, and bind a summary fact to the binders the claim opens with
//! as written ([`bind_facts_to_the_written_prefix`]).

mod aliases;
mod facts;
mod kinds;
mod places;
mod state;
mod typing;

pub use aliases::resolve_aliases_with;
pub(crate) use aliases::{resolve_aliases, resolve_aliases_keeping_calls};
pub use facts::bind_facts_to_the_written_prefix;
pub use kinds::{node_kinds, ExprKind, NodeKind, PatternKind};
pub use places::{
    first_dereference_of_a_non_reference, first_final_held_through_a_reference_parameter,
    first_final_of_a_value_not_named_as_a_borrow, first_unplaced_mut_ref_read, ParamReference,
};
pub use state::{
    applied_to_the_result, entry_reads_of_unchanging_params, in_the_old_dialect,
    place_parameter_reads, postcondition_at_a_call, postcondition_states, ClauseKind, Signature,
};
pub(crate) use typing::{
    dereferenced, elaborate, first_unmodeled_dereference, infer_name_uses, sort_of, Dereference,
};
pub use typing::{NativeNameUse, NativeUseSort};

use crate::formula::PureExpr;

/// The direct subterms of `expr`, in source order: a quantifier's body then
/// its triggers, a `match`'s scrutinee then each arm's body.
pub(crate) fn children(expr: &PureExpr) -> Vec<&PureExpr> {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(..) => Vec::new(),
        PureExpr::BinOp(left, _, right)
        | PureExpr::LetAssume {
            assumption: left,
            body: right,
        }
        | PureExpr::LetObligation {
            obligation: left,
            body: right,
        }
        | PureExpr::Let {
            value: left,
            body: right,
            ..
        } => vec![left, right],
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner)
        | PureExpr::Closure { body: inner, .. } => vec![inner],
        PureExpr::Ite(cond, then_expr, else_expr) => vec![cond, then_expr, else_expr],
        PureExpr::MethodCall { receiver, args, .. } => {
            std::iter::once(receiver.as_ref()).chain(args).collect()
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().collect(),
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            std::iter::once(body.as_ref())
                .chain(triggers.iter().flatten())
                .collect()
        }
        PureExpr::Match { scrutinee, arms } => std::iter::once(scrutinee.as_ref())
            .chain(arms.iter().map(|arm| &arm.body))
            .collect(),
    }
}
