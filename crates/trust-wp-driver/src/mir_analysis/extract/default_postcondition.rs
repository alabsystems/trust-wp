// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type-directed specialization for generic default postconditions.
//!
//! `trust-wp-std` keeps specs like `mem::take` generic (`Default::default()`) so
//! the contract remains reusable across monomorphizations. At call sites we can
//! often refine that placeholder to a concrete logical postcondition using the
//! instantiated Rust type.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Operand},
    ty::{Mutability, Ty, TyCtxt, TyKind},
};
use rustc_span::Spanned;
use trust_wp_driver::StdSpec;

const DEFAULT_PLACEHOLDER: &str = "Default::default()";

/// Specialize generic `Default::default()` postconditions using the concrete
/// call-site type.
///
/// Any std-spec postcondition containing the `Default::default()` placeholder
/// is eligible for specialization. The concrete type is inferred from the
/// first `&mut T` argument's pointee type (covers `mem::take`, `PredCell::take`,
/// `PermCell::take`, and any future spec that uses the same pattern). (#2256)
pub(in crate::mir_analysis::extract) fn specialize_default_postconditions_for_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    _def_id: DefId,
    spec: &mut StdSpec,
) {
    if !spec
        .ensures
        .iter()
        .any(|clause| clause.contains(DEFAULT_PLACEHOLDER))
    {
        return;
    }

    let Some(dest_pointee_ty) = first_call_arg_pointee_ty(body, args) else {
        return;
    };
    let dest_param_name = spec
        .param_names
        .as_deref()
        .and_then(|names| names.first())
        .cloned()
        .unwrap_or_else(|| "arg0".to_string());

    specialize_take_default_postcondition_for_ty(tcx, spec, &dest_param_name, dest_pointee_ty);
}

/// Replace any generic `Default::default()` placeholder in a spec's ensures
/// clauses with a concrete clause for the given destination type.
pub(in crate::mir_analysis::extract) fn specialize_take_default_postcondition_for_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    spec: &mut StdSpec,
    dest_param_name: &str,
    dest_pointee_ty: Ty<'tcx>,
) {
    let target_expr = format!("(^{dest_param_name})");
    let Some(specialized_clause) = default_clause_for_target_ty(tcx, &target_expr, dest_pointee_ty)
    else {
        return;
    };

    let mut specialized_any = false;
    for clause in &mut spec.ensures {
        if clause.contains(DEFAULT_PLACEHOLDER) {
            clause.clone_from(&specialized_clause);
            specialized_any = true;
        }
    }

    // Creusot-parity (F2): for `&mut [T]` destinations, the `Default`
    // postcondition has a SECOND conjunct — the final view of the default
    // borrow — which the single specialized clause above drops. Emit it as a
    // separate ensures clause, exactly as Creusot does.
    if specialized_any {
        if let Some(final_view_clause) =
            default_final_view_clause_for_target_ty(&target_expr, dest_pointee_ty)
        {
            if !spec.ensures.contains(&final_view_clause) {
                spec.ensures.push(final_view_clause);
            }
        }
    }
}

/// Final-view conjunct of the `Default` postcondition for `&mut` slice/str
/// destinations (Creusot-parity fix "F2").
///
/// Creusot's `mem::take` contract is `#[ensures(T::default.postcondition((),
/// ^dest))]` (creusot-std/src/std/mem.rs), and its `Default` spec for mutable
/// slice references has TWO conjuncts (creusot-std/src/std/slice.rs:429-433):
///
/// ```text
/// impl<'a, T> Default for &'a mut [T] {
///     #[ensures((*result)@ == Seq::empty())]
///     #[ensures((^result)@ == Seq::empty())]
///     fn default() -> &'a mut [T];
/// }
/// ```
///
/// With `result := ^dest`, the first conjunct maps to the existing
/// `(^dest)@ == Seq::empty()` clause (the view of a `&mut` borrow is the view
/// of its current target, like Creusot's `View for &mut T`). This helper
/// emits the second conjunct trust-wp previously dropped: the FINAL view of
/// the inner borrow, `(^(^dest))@ == Seq::empty()`.
///
/// Soundness: the default `&mut [T]`/`&mut str` is the empty slice/str; a
/// mutable reference cannot change the length of its referent, so the
/// prophecy (final value) of an empty default borrow is also empty. `&mut str`
/// has no `Default` spec in Creusot — it is included here as the symmetric
/// extension of the existing current-view Str handling, justified by the same
/// fixed-length argument. Shared `&[T]`/`&str` destinations get NO extra
/// clause: Creusot's `Default for &'a [T]` (slice.rs:436-440) has only the
/// single current-view conjunct, and a shared reference has no prophecy.
///
/// Pipeline note (replay-verified): in the nested mut-borrow encoding
/// (`&mut &mut [T]` dest, e.g. `take_first_mut`) this clause reaches the VC
/// as the intended `final_<dest>_final_view == seq_empty` fact, i.e.
/// `(^^dest)@ == Seq::empty()`. In straight-line callers,
/// `ssa_rename_call_assumptions` (contract_transform.rs Phase 5b, #2124)
/// treats the depth-2 `Final` chain as a sequential-mutation timeline and
/// re-points this clause at `(^dest)@` (demoting the depth-1 conjunct to an
/// SSA intermediate) — still a true fact there (with no later mutation,
/// `^dest` IS the post-take default), just not the nested-prophecy reading.
/// Adversarial gating (ensures(false) after take, with and without a
/// nonempty writeback `*dest = s`) confirms neither reading opens a
/// contradiction/false-accept channel.
fn default_final_view_clause_for_target_ty<'tcx>(
    target_expr: &str,
    ty: Ty<'tcx>,
) -> Option<String> {
    match ty.kind() {
        TyKind::Ref(_, inner, Mutability::Mut)
            if matches!(inner.kind(), TyKind::Slice(_) | TyKind::Str) =>
        {
            Some(format!("(^{target_expr})@ == Seq::empty()"))
        }
        _ => None,
    }
}

/// Build a concrete default-value postcondition for a specific target
/// expression and Rust type.
pub(in crate::mir_analysis::extract) fn default_clause_for_target_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    target_expr: &str,
    ty: Ty<'tcx>,
) -> Option<String> {
    match ty.kind() {
        TyKind::Bool => Some(format!("{target_expr} == false")),
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Char => Some(format!("{target_expr} == 0")),
        TyKind::Tuple(fields) if fields.is_empty() => Some(format!("{target_expr} == ()")),
        TyKind::Ref(_, inner, _) if matches!(inner.kind(), TyKind::Slice(_) | TyKind::Str) => {
            Some(format!("{target_expr}@ == Seq::empty()"))
        }
        TyKind::Adt(adt_def, _) => {
            let adt_path = tcx.def_path_str(adt_def.did());
            match adt_path.as_str() {
                "core::option::Option" | "std::option::Option" => {
                    Some(format!("{target_expr} == None()"))
                }
                "alloc::vec::Vec"
                | "std::vec::Vec"
                | "alloc::string::String"
                | "std::string::String" => Some(format!("{target_expr}@ == Seq::empty()")),
                _ if adt_path.ends_with("option::Option") => {
                    Some(format!("{target_expr} == None()"))
                }
                _ if adt_path.ends_with("vec::Vec") || adt_path.ends_with("string::String") => {
                    Some(format!("{target_expr}@ == Seq::empty()"))
                }
                "std::collections::HashMap"
                | "std::collections::hash_map::HashMap"
                | "std::collections::HashSet"
                | "std::collections::hash_set::HashSet" => {
                    Some(format!("{target_expr}@.len() == 0"))
                }
                _ if adt_path.ends_with("HashMap") || adt_path.ends_with("HashSet") => {
                    Some(format!("{target_expr}@.len() == 0"))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn first_call_arg_pointee_ty<'tcx>(
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
) -> Option<Ty<'tcx>> {
    let arg_ty = match &args.first()?.node {
        Operand::Copy(place) | Operand::Move(place) => body.local_decls[place.local].ty,
        Operand::Constant(constant) => constant.ty(),
        // RuntimeChecks, like Constant, references no place/local; it is a
        // `bool` flag operand that can never be a `&mut T` argument, so it
        // yields no pointee type (mirrors the Constant scalar-type path,
        // which falls through to `None` below).
        Operand::RuntimeChecks(_) => return None,
    };
    match arg_ty.kind() {
        TyKind::Ref(_, inner, _) => Some(*inner),
        _ => None,
    }
}
