// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-result resolution helpers for substitution extraction.
//!
//! These functions support the block-walking pipeline in [`super`].
//! `call_result_expr_for_substitutions` resolves function calls against user
//! specs, extern specs, and trait method fallbacks. `resolve_ref_to_named_local`
//! preserves mutable-reference variable identity.

use std::collections::HashMap;

use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, Place, ProjectionElem, Rvalue},
    ty::TyCtxt,
};
use rustc_span::Spanned;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::{
    super::{
        super::{
            call_resolve::{
                arg_names_for_def_id, extract_closure_def_id_from_fn_call,
                extract_fn_item_def_id_from_fn_trait_call, resolve_arg_names_or_warn,
            },
            effects::CallEffects,
            spec_apply::{
                self, apply_postconditions_with_effects, apply_postconditions_with_self_and_effects,
            },
            translate::{translate_operand, ty_to_expr_sort_enriched},
        },
        call_args::{
            call_result_symbol, derive_self_expr_from_args, normalize_extern_spec_self_expr,
            translate_call_args_for_substitutions_with_tcx,
        },
        call_resolve_shared::{
            classify_cell_builtin_path, recover_snapshot_capture_current_pointee, resolve_call,
            ResolvedCallKind,
        },
        call_resolve_util::extend_call_with_const_generic_args,
        closure::resolve_closure_arg_return_values,
        helpers::{expr_contains_final, source_name_for_local},
    },
    SubstitutionExtractionContext,
};
pub(super) fn call_result_expr_for_substitutions<'tcx>(
    ctx: &SubstitutionExtractionContext<'_, 'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    local_exprs: &HashMap<Local, PureExpr>,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: Local,
) -> PureExpr {
    let result_var = call_result_symbol(body, destination, ctx.tcx);

    let resolved = resolve_call(
        ctx.tcx,
        body,
        bb,
        func,
        args,
        destination,
        ctx.user_specs,
        ctx.trait_specs,
        ctx.extern_specs,
        None,
        local_exprs,
    );
    let cell_builtin = resolved
        .def_id
        .and_then(|def_id| classify_cell_builtin_path(&ctx.tcx.def_path_str(def_id)));

    if cell_builtin.is_some() {
        return result_var;
    }

    match resolved.kind {
        ResolvedCallKind::ArrayLen(len_expr) => len_expr,
        ResolvedCallKind::DirectSpec(spec) => {
            let def_id = resolved.def_id.expect("DirectSpec always has def_id");
            let mut translated_args = translate_call_args_for_substitutions_with_tcx(
                args,
                local_exprs,
                Some(body),
                Some(ctx.tcx),
            );
            resolve_closure_arg_return_values(ctx, body, args, &mut translated_args);
            let mut param_names =
                resolve_arg_names_or_warn(ctx.tcx, def_id, spec.param_names.as_ref());
            extend_call_with_const_generic_args(
                ctx.tcx,
                def_id,
                func,
                &mut translated_args,
                &mut param_names,
            );
            let param_names = (!param_names.is_empty()).then_some(param_names.as_slice());
            let mut effects = CallEffects::new();
            let resolved_expr = apply_postconditions_with_effects(
                &spec.ensures,
                &result_var,
                &translated_args,
                param_names,
                &mut effects,
                false,
            );
            let resolved_expr = if preserves_empty_seq_constructor_carrier(&resolved_expr) {
                result_var
            } else {
                resolved_expr
            };
            // See the ExternSpec branch / `recover_snapshot_capture_current_pointee`. (#682)
            recover_snapshot_capture_current_pointee(ctx.tcx, body, def_id, args, resolved_expr)
            // effects dropped — substitution pass; thread-locals cleared before main extraction
        }
        ResolvedCallKind::ExternSpec(spec) => {
            // Closure-aware resolution (#352): when the extern/std_specs match is a
            // Fn/FnOnce/FnMut trait call and the concrete closure has user specs,
            // use the closure's own spec with untupled arguments.
            let def_id = resolved.def_id.expect("ExternSpec always has def_id");
            let (effective_spec, effective_args, effective_param_names, effective_self_expr) =
                if let Some(closure_def_id) = extract_closure_def_id_from_fn_call(func) {
                    if let Some(closure_spec) = ctx.user_specs.get(&closure_def_id) {
                        let closure_args = translate_call_args_for_substitutions_with_tcx(
                            &args[1.min(args.len())..],
                            local_exprs,
                            Some(body),
                            Some(ctx.tcx),
                        );
                        let closure_param_names = arg_names_for_def_id(ctx.tcx, closure_def_id);
                        let closure_self_expr = args
                            .first()
                            .and_then(|arg| translate_operand(&arg.node, local_exprs));
                        (
                            closure_spec.clone(),
                            closure_args,
                            closure_param_names,
                            closure_self_expr,
                        )
                    } else {
                        resolve_extern_spec_args_for_subst(
                            ctx,
                            body,
                            func,
                            args,
                            local_exprs,
                            def_id,
                            &spec,
                        )
                    }
                } else if let Some(fn_def_id) = extract_fn_item_def_id_from_fn_trait_call(func) {
                    // Function item called through Fn trait dispatch (#1636)
                    if let Some(fn_spec) = ctx.user_specs.get(&fn_def_id) {
                        let fn_args = translate_call_args_for_substitutions_with_tcx(
                            &args[1.min(args.len())..],
                            local_exprs,
                            Some(body),
                            Some(ctx.tcx),
                        );
                        let fn_param_names = arg_names_for_def_id(ctx.tcx, fn_def_id);
                        (fn_spec.clone(), fn_args, fn_param_names, None)
                    } else {
                        resolve_extern_spec_args_for_subst(
                            ctx,
                            body,
                            func,
                            args,
                            local_exprs,
                            def_id,
                            &spec,
                        )
                    }
                } else {
                    resolve_extern_spec_args_for_subst(
                        ctx,
                        body,
                        func,
                        args,
                        local_exprs,
                        def_id,
                        &spec,
                    )
                };
            let mut effects = CallEffects::new();
            let resolved_expr = apply_postconditions_with_self_and_effects(
                &effective_spec.ensures,
                &result_var,
                &effective_args,
                effective_param_names.as_deref(),
                effective_self_expr.as_ref(),
                &mut effects,
            );
            let resolved_expr = if preserves_empty_seq_constructor_carrier(&resolved_expr) {
                result_var
            } else {
                resolved_expr
            };
            // `snapshot!(*a)` of a `&mut T` deref resolves through this extern
            // `Snapshot::capture` spec. Freeze the CURRENT pointee value at the
            // capture point instead of aliasing the mut-ref identity (which the
            // substitution pass later advances to its prophecy/final after the
            // intervening `add_some(a)` call). Without this, `*a_p` follows
            // `^a` and `*a > *a_p` collapses to `^a > ^a` (unprovable). (#682)
            recover_snapshot_capture_current_pointee(ctx.tcx, body, def_id, args, resolved_expr)
            // effects dropped — substitution pass; thread-locals cleared before main extraction
        }
        ResolvedCallKind::BoxNew => {
            // Alias-preserving fallback for Box::new.
            args.first()
                .and_then(|arg| translate_operand(&arg.node, local_exprs))
                .unwrap_or(result_var)
        }
        ResolvedCallKind::IntPassthrough(expr) | ResolvedCallKind::LayoutIntrinsic(expr) => expr,
        ResolvedCallKind::MappingFromClosure
        | ResolvedCallKind::MapInvFromClosure
        | ResolvedCallKind::TryBranch
        | ResolvedCallKind::Opaque => {
            // Substitution pipeline does not handle try-operator;
            // fall through to opaque result variable.
            result_var
        }
    }
}

fn preserves_empty_seq_constructor_carrier(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if args.is_empty() && matches!(name.as_str(), "seq_empty" | "Seq::empty")
    )
}

/// Helper to translate args and resolve param names for extern spec application
/// in the substitution pipeline. Used for both non-closure and closure-without-user-spec
/// branches to avoid code duplication.
#[allow(clippy::type_complexity)]
fn resolve_extern_spec_args_for_subst<'tcx>(
    ctx: &SubstitutionExtractionContext<'_, 'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_exprs: &HashMap<Local, PureExpr>,
    def_id: rustc_hir::def_id::DefId,
    spec: &trust_wp_driver::StdSpec,
) -> (
    trust_wp_driver::StdSpec,
    Vec<spec_apply::TranslatedArg>,
    Option<Vec<String>>,
    Option<PureExpr>,
) {
    let mut translated_args = translate_call_args_for_substitutions_with_tcx(
        args,
        local_exprs,
        Some(body),
        Some(ctx.tcx),
    );
    resolve_closure_arg_return_values(ctx, body, args, &mut translated_args);
    let mut param_names = resolve_arg_names_or_warn(ctx.tcx, def_id, spec.param_names.as_ref());
    extend_call_with_const_generic_args(
        ctx.tcx,
        def_id,
        func,
        &mut translated_args,
        &mut param_names,
    );
    let param_names = (!param_names.is_empty()).then_some(param_names);
    let self_expr = normalize_extern_spec_self_expr(
        &ctx.tcx.def_path_str(def_id),
        derive_self_expr_from_args(&translated_args),
    );
    (spec.clone(), translated_args, param_names, self_expr)
}

/// For mutable reference creation, resolve the reference target to a source
/// variable name. Returns `Some(Var(name))` if the reference preserves a
/// source variable identity, `None` otherwise.
///
/// This handles three MIR patterns:
/// 1. `_N = &mut _M` where `_M` has source name "x" → `Var("x")`
/// 2. `_N = &mut (*_M)` (reborrow) where `_M` already maps to `Var("x")` → `Var("x")`
/// 3. Otherwise → `None` (fall through to regular translate_rvalue)
///
/// By storing `Var(name)` for reference locals, variable identity is preserved
/// through tuple construction and call postconditions, enabling projected deref
/// writes like `*swap_refs((&mut a, &mut b)).0 = 10` to resolve back to `b`. (#746)
/// Resolve a `&mut` rvalue to the named local it references, using enriched
/// ADT sort resolution via the provided `TyCtxt`.
pub(super) fn resolve_ref_to_named_local<'tcx>(
    rvalue: &Rvalue<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    local_exprs: &HashMap<Local, PureExpr>,
    tcx: TyCtxt<'tcx>,
) -> Option<PureExpr> {
    let Rvalue::Ref(_, _, ref_place) = rvalue else {
        return None;
    };

    if ref_place.projection.is_empty() {
        let name = source_name_for_local(body, ref_place.local, arg_names)?;
        if let Some(expr) = local_exprs.get(&ref_place.local) {
            if expr_contains_final(expr) {
                return Some(expr.clone());
            }
            if let PureExpr::Var(var_name, _) = expr {
                if var_name != &name {
                    return Some(expr.clone());
                }
            }
        }
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[ref_place.local].ty);
        return Some(PureExpr::Var(name, sort));
    }

    if should_use_projected_reborrow_carrier(ref_place, body, local_exprs, tcx) {
        let carrier_sort = projected_reborrow_sort(ref_place, body, tcx);
        return Some(PureExpr::Var(
            projected_reborrow_carrier_name(ref_place),
            carrier_sort,
        ));
    }

    if ref_place.projection.len() == 1
        && matches!(ref_place.projection.first(), Some(ProjectionElem::Deref))
    {
        // Reborrow: `&mut (*_M)` — propagate the identity from _M.
        // When _M has been advanced to a post-state expression (containing
        // `Final` nodes from a prior mutating call), preserve the advanced
        // state so sequential calls receive the updated receiver. (#1597)
        if let Some(expr) = local_exprs.get(&ref_place.local) {
            if expr_contains_final(expr) {
                return Some(expr.clone());
            }
            if let PureExpr::Var(name, sort) = expr {
                return Some(PureExpr::Var(name.clone(), sort.clone()));
            }
        }
    }

    None
}

fn should_use_projected_reborrow_carrier<'tcx>(
    ref_place: &Place<'tcx>,
    body: &Body<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let has_deref = ref_place
        .projection
        .iter()
        .any(|proj| matches!(proj, ProjectionElem::Deref));
    if !has_deref {
        return false;
    }

    // Keep the established `&mut *x -> x` behavior for plain `&mut T`
    // reborrows. The synthetic carrier lane is only for nested/projected
    // mutable-reference identity such as `&mut *x` where `x: &mut &mut T`
    // or `&mut (*x).field`.
    if ref_place.projection.len() > 1 {
        return true;
    }

    let base_sort = local_exprs
        .get(&ref_place.local)
        .and_then(expr_sort)
        .or_else(|| ty_to_expr_sort_enriched(tcx, body.local_decls[ref_place.local].ty));
    matches!(
        base_sort.as_ref(),
        Some(ExprSort::MutRef(inner)) if matches!(inner.as_ref(), ExprSort::MutRef(_))
    )
}

fn projected_reborrow_sort<'tcx>(
    ref_place: &Place<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<ExprSort> {
    let inner_sort = ty_to_expr_sort_enriched(tcx, ref_place.ty(body, tcx).ty)?;
    Some(ExprSort::MutRef(Box::new(inner_sort)))
}

fn projected_reborrow_carrier_name(place: &Place<'_>) -> String {
    let projection_suffix = place
        .projection
        .iter()
        .map(|proj| projected_reborrow_projection_segment(&proj))
        .collect::<Vec<_>>()
        .join("_");
    format!(
        "__trust_wp_reborrow_{}_{}",
        place.local.as_u32(),
        projection_suffix
    )
}

fn projected_reborrow_projection_segment(
    proj: &ProjectionElem<Local, rustc_middle::ty::Ty<'_>>,
) -> String {
    match proj {
        ProjectionElem::Deref => "deref".to_string(),
        ProjectionElem::Field(field, _) => format!("field{}", field.as_u32()),
        ProjectionElem::Downcast(_, variant) => format!("downcast{}", variant.as_u32()),
        ProjectionElem::Index(local) => format!("index{}", local.as_u32()),
        ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => format!("const{offset}_{min_length}_{}", u8::from(*from_end)),
        ProjectionElem::Subslice { from, to, from_end } => {
            format!("subslice{from}_{to}_{}", u8::from(*from_end))
        }
        ProjectionElem::OpaqueCast(_) => "opaque".to_string(),
        ProjectionElem::UnwrapUnsafeBinder(_) => "unwrap".to_string(),
    }
}

fn expr_sort(expr: &PureExpr) -> Option<ExprSort> {
    match expr {
        PureExpr::Var(_, sort) => sort.clone(),
        PureExpr::Final(inner) | PureExpr::Old(inner) | PureExpr::View(inner) => expr_sort(inner),
        _ => None,
    }
}
