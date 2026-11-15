// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The type invariant of a generic parameter, and what it becomes at a call.
//!
//! Creusot gives every parameter `x: T` the precondition `inv(x)`, a type
//! parameter included, where `inv` at `T` is an opaque predicate the call site
//! instantiates. A generic body therefore holds `inv_T(t)` as a premise, a
//! trait call inside it with `Self = T` owes `inv_T(t)`, and the call that
//! FIXES `T` owes the invariant of the type it fixes it to. Without that last
//! step a generic hop launders any value into an impl body that was granted
//! `inv(self)` — the grant nobody paid for.
//!
//! Two consumers read [`type_param_invariant_at`]: the call site that owes a
//! body's grant at the body's instantiation, and the covering check that asks
//! whether a trait declaration's clause, instantiated at an impl, states what
//! that impl was granted. Soundness rests on the two reading ONE function:
//! whatever it answers for a type, a call fixing a parameter to that type owes
//! exactly that, and an impl is covered only by exactly that.

use std::{cell::RefCell, collections::HashSet, sync::Arc};

use rustc_middle::ty::{GenericArgs, Mutability, Ty, TyCtxt, TyKind};
use trust_wp_core::{
    formula::{BinOp, Pattern, PureExpr},
    logic::{type_param_invariant_index, type_param_invariant_method_name},
};

use super::lookup::has_trivial_type_invariant;

thread_local! {
    /// The invariant-bearing type names of THIS compilation session, the same
    /// set the parameter-clause builder resolves an ADT's method against.
    /// Session-scoped like every cache in `thread_locals`: installed once the
    /// definitions are final, cleared by `CacheGuard`.
    static INVARIANT_TYPE_NAMES: RefCell<Option<Arc<HashSet<String>>>> =
        const { RefCell::new(None) };
}

/// Install the session's invariant-bearing type names.
pub(in crate::callbacks) fn install_invariant_type_names(
    type_invariant_defs: &[trust_wp_core::logic::TypeInvariantDef],
) {
    let names: HashSet<String> = type_invariant_defs
        .iter()
        .map(|d| d.type_name().to_string())
        .collect();
    INVARIANT_TYPE_NAMES.with(|slot| *slot.borrow_mut() = Some(Arc::new(names)));
}

/// Forget the session's names (`CacheGuard`).
pub(crate) fn clear_invariant_type_names() {
    INVARIANT_TYPE_NAMES.with(|slot| *slot.borrow_mut() = None);
}

/// The clause a value of type `ty` is granted when that type is a type
/// parameter, held by value or behind one reference: `receiver` is handed the
/// reference's mutability (`None` by value) and builds the term the clause is
/// about, exactly as the pass it is called from does for an ADT there.
///
/// A `&mut T` holds only the ENTRY half of Creusot's pair. The final-value
/// half (`inv(^x)`) is a goal of the body and never a premise of any caller —
/// no call site reads it back — so leaving it out drops a check nobody's
/// proof rests on, while the entry half is paid for where `T` is fixed.
pub(super) fn type_param_invariant_clause(
    ty: Ty<'_>,
    receiver: impl FnOnce(Option<Mutability>) -> PureExpr,
) -> Option<PureExpr> {
    let (inner, access) = match ty.kind() {
        TyKind::Ref(_, inner, mutability) => (*inner, Some(*mutability)),
        _ => (ty, None),
    };
    let TyKind::Param(param) = inner.kind() else {
        return None;
    };
    Some(PureExpr::MethodCall {
        receiver: Arc::new(receiver(access)),
        method: type_param_invariant_method_name(param.index, param.name.as_str()),
        args: vec![],
    })
}

/// Whether `clause` states a type parameter's invariant anywhere inside it —
/// bare, on a tuple field, or in the arm of an enum decomposition.
pub(crate) fn mentions_type_param_invariant(clause: &PureExpr) -> bool {
    trust_wp_core::logic::mentions_type_param_invariant(clause)
}

/// Whether `ty` carries no invariant at any instantiation — a primitive, or a
/// tuple of them — so no body is ever granted anything at it.
pub(crate) fn is_trivially_invariant_free(ty: Ty<'_>) -> bool {
    has_trivial_type_invariant(ty)
}

/// Whether `clause` is a type-parameter invariant, and of which parameter.
pub(crate) fn type_param_invariant_of(clause: &PureExpr) -> Option<u32> {
    match clause {
        PureExpr::MethodCall { method, args, .. } if args.is_empty() => {
            type_param_invariant_index(method)
        }
        _ => None,
    }
}

/// What a type-parameter invariant clause becomes once its parameter is `ty`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum TypeParamInvariantAt {
    /// No part of a value of `ty` can carry an invariant.
    Nothing,
    /// The clause to state, over the original receiver.
    Clause(PureExpr),
    /// The clauses a body at `ty` is granted pass over a part that may carry
    /// an invariant, or `ty` does not determine the body a later hop enters —
    /// a trait object dispatches to its erased type's impl, and an
    /// unnormalized projection names no type at all.
    Unstatable,
}

/// Instantiate one type-parameter invariant clause at `ty`.
///
/// The answer is what the parameter-clause builder grants a parameter of type
/// `ty` whose value is the clause's receiver — the SAME function
/// (`clauses::param_clauses`) the builder states every body's premise with, so
/// a call fixing a parameter to `ty` owes exactly what a body entered at `ty`
/// holds: `inv(*r)` of the referent for `&X` (a shared reference is
/// transparent) and for `&mut X`, the fields of a tuple, the payloads of an
/// enum, the method of an invariant-bearing ADT.
///
/// The final-value half of `&mut X` is not owed: the builder states `inv(^x)`
/// as a GOAL of the body, never as a premise of any body, so no proof rests on
/// it, and a caller of a fresh borrow has nothing to prove it from.
///
/// [`TypeParamInvariantAt::Unstatable`] wherever those clauses pass over a
/// part of the value that may carry an invariant — a `Box`, an array, a
/// sequence container, a plain struct holding one, a trait object, a
/// projection. A body entered at such a type can hold (or need) a premise the
/// clauses do not state; owing less than that is how the caller that broke
/// the value got credited, so the call refuses instead. `Nothing` only where
/// no part of the value can carry an invariant at all.
pub(crate) fn type_param_invariant_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    clause: &PureExpr,
) -> TypeParamInvariantAt {
    let PureExpr::MethodCall { receiver, .. } = clause else {
        return TypeParamInvariantAt::Unstatable;
    };
    let Some(names) = INVARIANT_TYPE_NAMES.with(|slot| slot.borrow().clone()) else {
        return TypeParamInvariantAt::Unstatable;
    };
    let stated = super::clauses::param_clauses(tcx, ty, receiver, &names);
    if !stated.states_every_part {
        return TypeParamInvariantAt::Unstatable;
    }
    let Some(conjoined) = stated
        .premise()
        .into_iter()
        .reduce(|lhs, rhs| PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs)))
    else {
        return TypeParamInvariantAt::Nothing;
    };
    // A payload binder of the stated match that the receiver also names would
    // be captured inside the arm: the clause would state the payload's
    // invariant about some other term.
    let receiver_names = receiver.free_vars();
    if conjoined.any_recursive(|node| {
        matches!(node, PureExpr::Match { arms, .. }
            if arms.iter().any(|arm| pattern_binds_any(&arm.pattern, &receiver_names)))
    }) {
        return TypeParamInvariantAt::Unstatable;
    }
    TypeParamInvariantAt::Clause(conjoined)
}

fn pattern_binds_any(pattern: &Pattern, names: &HashSet<String>) -> bool {
    match pattern {
        Pattern::Binding(name) => names.contains(name),
        Pattern::Alias { alias, pattern } => {
            names.contains(alias) || pattern_binds_any(pattern, names)
        }
        Pattern::Constructor { inner, .. } => inner
            .as_deref()
            .is_some_and(|inner| pattern_binds_any(inner, names)),
        Pattern::Tuple(patterns) => patterns.iter().any(|p| pattern_binds_any(p, names)),
        Pattern::Wildcard | Pattern::Literal(_) => false,
        // A pattern shape this walk does not know may bind anything.
        _ => true,
    }
}

/// Instantiate every type-parameter invariant in `clauses` at `args`, the
/// generic arguments of the item the clauses were built under, wherever in a
/// clause it sits. One that states nothing becomes `true`, and a clause left
/// with nothing but `true` is dropped. `None` when a parameter has no type in
/// `args`, or its instantiation is [`TypeParamInvariantAt::Unstatable`].
pub(crate) fn instantiate_type_param_invariants<'tcx>(
    tcx: TyCtxt<'tcx>,
    clauses: &[PureExpr],
    args: GenericArgs<'tcx>,
) -> Option<Vec<PureExpr>> {
    let mut out = Vec::with_capacity(clauses.len());
    for clause in clauses {
        if !mentions_type_param_invariant(clause) {
            out.push(clause.clone());
            continue;
        }
        let unstatable = std::cell::Cell::new(false);
        let instantiated = clause.rewrite_bottom_up(|node| {
            let Some(index) = type_param_invariant_of(&node) else {
                return node;
            };
            let Some(ty) = args.get(index as usize).and_then(|arg| arg.as_type()) else {
                unstatable.set(true);
                return node;
            };
            match type_param_invariant_at(tcx, ty, &node) {
                TypeParamInvariantAt::Nothing => PureExpr::Bool(true),
                TypeParamInvariantAt::Clause(stated) => stated,
                TypeParamInvariantAt::Unstatable => {
                    unstatable.set(true);
                    node
                }
            }
        });
        if unstatable.get() {
            return None;
        }
        if !is_vacuous(&instantiated) {
            out.push(instantiated);
        }
    }
    Some(out)
}

/// `true`, or a match every arm of which is `true`.
fn is_vacuous(clause: &PureExpr) -> bool {
    match clause {
        PureExpr::Bool(true) => true,
        PureExpr::Match { arms, .. } => arms.iter().all(|arm| is_vacuous(&arm.body)),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use trust_wp_core::formula::{MatchArm, Pattern};

    use super::*;

    fn marker(receiver: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: type_param_invariant_method_name(0, "T"),
            args: vec![],
        }
    }

    fn some_none_match(some_body: PureExpr) -> PureExpr {
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("o".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    },
                    body: some_body,
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Bool(true),
                },
            ],
        }
    }

    #[test]
    fn a_nested_type_parameter_invariant_is_found() {
        // The instantiating call must see a clause inside an enum arm: missing
        // it would hand the callee's own generics to the caller unresolved.
        let nested = some_none_match(marker(PureExpr::Var("x".to_string(), None)));
        assert!(mentions_type_param_invariant(&nested));
        assert_eq!(type_param_invariant_of(&nested), None, "not a bare clause");
        let concrete = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
            method: trust_wp_core::logic::type_invariant_method_name("Sum10"),
            args: vec![],
        };
        assert!(!mentions_type_param_invariant(&concrete));
    }

    #[test]
    fn only_a_clause_that_states_nothing_is_vacuous() {
        assert!(is_vacuous(&PureExpr::Bool(true)));
        assert!(is_vacuous(&some_none_match(PureExpr::Bool(true))));
        assert!(!is_vacuous(&some_none_match(marker(PureExpr::Var(
            "x".to_string(),
            None
        )))));
        assert!(!is_vacuous(&PureExpr::Bool(false)));
    }
}
