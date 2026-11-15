// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The per-parameter arguments of a `Fn*` call to a concrete closure.

use std::collections::HashSet;

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeVisitableExt};
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_arity},
    PureExpr,
};

use super::mut_ref_spec::ty_exposes_interior_mutability;
use crate::mir_analysis::spec_apply::TranslatedArg;

/// The arguments a `Fn*::call*` hands `closure_def_id`, one per closure
/// parameter, from `args`: the call's translated arguments after the receiver.
///
/// A call passes a closure's parameters as ONE tuple after the receiver (the
/// `rust-call` ABI), while the closure's clauses name each parameter and its
/// own lane reads each as a local of its own. Tuple lowering already makes a
/// tuple of one its element, and a closure of no parameters reads none; for
/// two or more, parameter `i` is field `i` of the tuple, the value the
/// closure's own lane reads for it. Bound whole, the tuple stood for the first
/// parameter and every other one was read by nothing.
///
/// Untupled only when every parameter is a value no call writes through: its
/// type reaches no `&mut`, no `*mut`, no interior-mutable memory and no type
/// parameter or alias (either may be instantiated at one). A closure's call
/// advances only its receiver (`resolved_call_spec_mutating_ref_arg_positions`),
/// never a `&mut` inside the tuple, so a clause over such a parameter has no
/// reading at the call. For a closure of two or more parameters that is not
/// untupled no parameter is bound at all (the tuple is no parameter's value):
/// a clause that names one stays unbound and the call fails closed.
pub(in crate::mir_analysis::extract) fn untupled_closure_call_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    closure_def_id: DefId,
    args: Vec<TranslatedArg>,
) -> Vec<TranslatedArg> {
    let [tupled] = args.as_slice() else {
        return args;
    };
    match closure_params(tcx, closure_def_id) {
        Some((arity, true)) if arity >= 2 => untuple(tupled, arity).unwrap_or_default(),
        Some((arity, false)) if arity >= 2 => Vec::new(),
        _ => args,
    }
}

/// The closure's parameter count, and whether every parameter is a value no
/// call writes through (see [`untupled_closure_call_args`]). `None` when its
/// signature is not a closure's.
fn closure_params(tcx: TyCtxt<'_>, closure_def_id: DefId) -> Option<(usize, bool)> {
    if !matches!(tcx.def_kind(closure_def_id), DefKind::Closure) {
        return None;
    }
    let closure_ty = tcx
        .type_of(closure_def_id)
        .instantiate_identity()
        .skip_norm_wip();
    let TyKind::Closure(_, closure_args) = closure_ty.kind() else {
        return None;
    };
    let sig = tcx.liberate_late_bound_regions(closure_def_id, closure_args.as_closure().sig());
    let TyKind::Tuple(params) = sig.inputs().first()?.kind() else {
        return None;
    };
    let typing_env = ty::TypingEnv::post_analysis(tcx, closure_def_id);
    let values = params.iter().all(|param| {
        !param.has_param()
            && !param.has_aliases()
            && !reaches_writable_pointer(tcx, param, 0, &mut HashSet::new())
            && !ty_exposes_interior_mutability(tcx, typing_env, param)
    });
    Some((params.len(), values))
}

const WRITABLE_POINTER_DEPTH_BOUND: usize = 6;

/// Whether a value of `ty` reaches a `&mut` or a `*mut`, through its generic
/// arguments and its fields. `true` past the depth bound, where the walk
/// stops seeing.
fn reaches_writable_pointer<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    depth: usize,
    seen: &mut HashSet<Ty<'tcx>>,
) -> bool {
    if depth > WRITABLE_POINTER_DEPTH_BOUND {
        return true;
    }
    if !seen.insert(ty) {
        return false;
    }
    ty.walk()
        .filter_map(|arg| arg.as_type())
        .any(|inner| match inner.kind() {
            TyKind::Ref(_, _, ty::Mutability::Mut) | TyKind::RawPtr(_, ty::Mutability::Mut) => true,
            TyKind::Adt(adt, args) => adt.all_fields().any(|field| {
                reaches_writable_pointer(tcx, field.ty(tcx, *args).skip_norm_wip(), depth + 1, seen)
            }),
            _ => false,
        })
}

/// Field `i` of the argument tuple, for each of `arity` parameters: the
/// tuple's own element when it is a tuple literal of that arity, its field
/// projection otherwise. `None` for a tuple literal of another arity, which
/// no call of this closure builds; the caller then binds no parameter.
fn untuple(tupled: &TranslatedArg, arity: usize) -> Option<Vec<TranslatedArg>> {
    let elements: Vec<PureExpr> = match &tupled.expr {
        PureExpr::LogicFnCall { name, args } if tuple_logic_fn_arity(name).is_some() => {
            if tuple_logic_fn_arity(name) != Some(arity) || args.len() != arity {
                return None;
            }
            args.clone()
        }
        tuple => (0..arity)
            .map(|index| PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(index),
                args: vec![tuple.clone()],
            })
            .collect(),
    };
    Some(
        elements
            .into_iter()
            .map(|expr| TranslatedArg {
                expr,
                is_fallback: tupled.is_fallback,
                exact_callable_value: false,
                stale: tupled.stale,
            })
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    #[test]
    fn a_tuple_literal_gives_each_parameter_its_element() {
        let tupled = TranslatedArg::new(PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(2),
            args: vec![PureExpr::Int(4), var("y")],
        });
        let untupled = untuple(&tupled, 2).expect("arity matches");
        let exprs: Vec<PureExpr> = untupled.iter().map(|arg| arg.expr.clone()).collect();
        assert_eq!(exprs, vec![PureExpr::Int(4), var("y")]);
        assert!(untupled.iter().all(|arg| !arg.is_fallback && !arg.stale));
    }

    #[test]
    fn any_other_tuple_gives_each_parameter_its_field_projection() {
        let tupled = TranslatedArg::new(var("t"));
        let untupled = untuple(&tupled, 2).expect("projectable");
        assert_eq!(
            untupled[1].expr,
            PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(1),
                args: vec![var("t")],
            }
        );
    }

    #[test]
    fn a_tuple_literal_of_another_arity_is_not_untupled() {
        let tupled = TranslatedArg::new(PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(3),
            args: vec![PureExpr::Int(1), PureExpr::Int(2), PureExpr::Int(3)],
        });
        assert!(untuple(&tupled, 2).is_none());
    }

    #[test]
    fn each_parameter_inherits_the_tuple_s_fallback_and_staleness() {
        let mut tupled = TranslatedArg::fallback(var("$fallback"));
        tupled.stale = true;
        let untupled = untuple(&tupled, 3).expect("projectable");
        assert_eq!(untupled.len(), 3);
        assert!(untupled.iter().all(|arg| arg.is_fallback && arg.stale));
    }
}
