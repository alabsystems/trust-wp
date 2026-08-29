// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure capture tracking and mutation state propagation.
//!
//! This module handles:
//! - Detecting closure-mutating calls (`FnMut::call_mut`, `FnOnce::call_once`)
//! - Resolving closure capture variable names from MIR
//! - Propagating post-call state through closure environment projections
//! - Substituting capture field references in postconditions
//! - Advancing `&mut T` deref state after mutating calls

use std::{collections::HashMap, sync::Arc};

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{Body, Local, Operand},
    ty::TyCtxt,
};
use rustc_span::Spanned;
use trust_wp_core::formula::{internal::tuple_lowering::tuple_logic_fn_arity, PureExpr};
use trust_wp_driver::{lookup_spec_with_extern, StdSpec};

use super::{
    extract_return_expr_with_context_detailed, helpers::source_name_for_local,
    SubstitutionExtractionContext,
};
pub(super) use crate::callbacks::final_receiver_state_expr;
use crate::{
    callbacks::strip_receiver_state_wrappers,
    mir_analysis::{
        call_resolve::{
            extract_call_def_id, resolve_arg_names_or_warn, resolve_trait_method_def_id,
        },
        effects::CallEffects,
        spec_apply::TranslatedArg,
        translate::translate_operand,
    },
};

mod mut_ref_spec;
mod postcondition_substitution;

#[cfg(test)]
pub(super) use mut_ref_spec::spec_mentions_post_state_for_aliases;
pub(super) use mut_ref_spec::{
    all_mut_ref_arg_positions, resolved_call_mutating_ref_arg_positions,
    spec_mutates_closure_state, spec_mutating_ref_arg_positions,
};
pub(super) use postcondition_substitution::{
    project_capture_field, substitute_capture_fields_in_postcondition,
};

/// For closure arguments whose translation failed (fallback), try to extract
/// the closure's return expression from its MIR body. This enables postcondition
/// specs that call closure parameters (e.g., `err()` in `ok_or_else`) to resolve
/// to concrete values when the closure is a simple non-capturing closure like
/// `|| true`. (#1277)
pub(super) fn resolve_closure_arg_return_values<'tcx>(
    ctx: &SubstitutionExtractionContext<'_, 'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    translated_args: &mut [TranslatedArg],
) {
    for (idx, arg) in args.iter().enumerate() {
        let Some(_ta) = translated_args.get(idx) else {
            continue;
        };
        // Check if the argument's type is a closure
        let local = match &arg.node {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => continue,
        };
        let ty = body.local_decls[local].ty;
        let rustc_middle::ty::TyKind::Closure(closure_def_id, _) = ty.kind() else {
            continue;
        };
        // Inline consts can appear in call arguments with closure-like typing
        // shapes but do not support `optimized_mir`. Keep this path strictly
        // for real closures.
        if !matches!(ctx.tcx.def_kind(*closure_def_id), DefKind::Closure) {
            continue;
        }
        // Try to extract the closure's return expression from its MIR body
        let Some(closure_body) = ctx
            .tcx
            .is_mir_available(*closure_def_id)
            .then(|| ctx.tcx.optimized_mir(*closure_def_id))
        else {
            continue;
        };
        let closure_arg_names = resolve_arg_names_or_warn(ctx.tcx, *closure_def_id, None);
        // Best-effort closure-arg enrichment: if extraction fails we keep the
        // existing fallback argument rather than surfacing a warning here.
        let return_expr = extract_return_expr_with_context_detailed(
            ctx.tcx,
            closure_body,
            &closure_arg_names,
            ctx.user_specs,
            ctx.trait_specs,
            ctx.extern_specs,
        )
        .value;
        if let Some(ret) = return_expr {
            translated_args[idx] = TranslatedArg::new(ret);
        }
    }
}

pub(super) fn call_mutates_closure_state<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
    fn is_mutating_call_path(path: &str) -> bool {
        path.contains("FnMut::call_mut")
            || path.contains("FnOnce::call_once")
            || path.ends_with("::call_mut")
            || path.ends_with("::call_once")
    }

    let Some(def_id) = extract_call_def_id(func) else {
        return false;
    };
    let path = tcx.def_path_str(def_id);
    if is_mutating_call_path(&path) {
        return true;
    }
    resolve_trait_method_def_id(tcx, def_id).is_some_and(|trait_method_id| {
        let trait_path = tcx.def_path_str(trait_method_id);
        is_mutating_call_path(&trait_path)
    })
}

pub(super) fn closure_capture_names_for_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Option<Vec<String>> {
    let local_def_id = body.source.def_id().as_local()?;
    if tcx.def_kind(local_def_id.to_def_id()) != DefKind::Closure {
        return None;
    }

    let saved_names: Vec<String> = tcx
        .closure_saved_names_of_captured_variables(local_def_id.to_def_id())
        .iter()
        .map(|symbol| symbol.as_str().to_string())
        .collect();

    let capture_names = tcx
        .closure_captures(local_def_id)
        .iter()
        .enumerate()
        .map(|(idx, capture)| {
            let var_ident_name = capture.var_ident.as_str().to_string();
            if !var_ident_name.is_empty() && var_ident_name != "_" {
                return var_ident_name;
            }

            let symbol_name = capture.to_symbol().to_string();
            if !symbol_name.is_empty() && symbol_name != "_" {
                return symbol_name;
            }

            saved_names
                .get(idx)
                .filter(|name| !name.is_empty() && name.as_str() != "_")
                .cloned()
                .unwrap_or_else(|| format!("self.{idx}"))
        })
        .collect();

    Some(capture_names)
}

pub(super) fn closure_capture_name_from_projected_var(
    projected_name: &str,
    capture_names: Option<&[String]>,
) -> Option<String> {
    let capture_names = capture_names?;
    // Primary path: `self.N` → capture_names[N]
    if let Some(field_path) = projected_name.strip_prefix("self.") {
        let field_idx_segment = field_path.split('.').next()?;
        let field_idx = field_idx_segment.parse::<usize>().ok()?;
        return capture_names.get(field_idx).cloned();
    }
    // Deref-prefixed variant: `*self.N` → capture_names[N] (for deref
    // substitution keys generated from double-deref writes in closures).
    if let Some(field_path) = projected_name.strip_prefix("*self.") {
        let field_idx_segment = field_path.split('.').next()?;
        let field_idx = field_idx_segment.parse::<usize>().ok()?;
        return capture_names.get(field_idx).map(|name| format!("*{name}"));
    }
    // Carrier name fallback (#2691): projected reborrow carriers like
    // `__trust_wp_reborrow_N_deref_fieldM` encode the capture field index
    // in the `fieldM` suffix. When the carrier refers to `_1` (self),
    // extract M and resolve through capture_names.
    if let Some(carrier_suffix) = projected_name.strip_prefix("__trust_wp_reborrow_") {
        return resolve_carrier_field_to_capture_name(carrier_suffix, capture_names);
    }
    // Deref-prefixed carrier variant: `*__trust_wp_reborrow_N_deref_fieldM`
    if let Some(carrier_suffix) = projected_name.strip_prefix("*__trust_wp_reborrow_") {
        return resolve_carrier_field_to_capture_name(carrier_suffix, capture_names)
            .map(|name| format!("*{name}"));
    }
    None
}

/// Resolve a reborrow carrier suffix to a capture name.
///
/// Carrier format: `{local_index}_{projection_suffix}` where projection_suffix
/// contains `fieldN` segments. Extract the FIRST field index and map through
/// capture names. Only resolves carriers that reference `_1` (local index 1,
/// which is `self` in closure MIR).
fn resolve_carrier_field_to_capture_name(
    carrier_suffix: &str,
    capture_names: &[String],
) -> Option<String> {
    // The carrier suffix format is: `1_deref_field0` (local_1, projection [Deref, Field(0)])
    // We need to extract the field index from the `fieldN` component.
    for segment in carrier_suffix.split('_') {
        if let Some(idx_str) = segment.strip_prefix("field") {
            let field_idx = idx_str.parse::<usize>().ok()?;
            return capture_names.get(field_idx).cloned();
        }
    }
    None
}

pub(super) fn record_name_update_with_capture_alias(
    name_updates: &mut HashMap<String, PureExpr>,
    projected_name: &str,
    expr: &PureExpr,
    capture_names: Option<&[String]>,
) {
    if let Some(capture_name) =
        closure_capture_name_from_projected_var(projected_name, capture_names)
    {
        name_updates.insert(capture_name, expr.clone());
    }
    name_updates.insert(projected_name.to_string(), expr.clone());
}

pub(super) fn call_mutates_via_contract<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> bool {
    let Some(def_id) = extract_call_def_id(func) else {
        return false;
    };

    if user_specs
        .get(&def_id)
        .is_some_and(spec_mutates_closure_state)
    {
        return true;
    }
    if trait_specs
        .get(&def_id)
        .is_some_and(spec_mutates_closure_state)
    {
        return true;
    }

    // Phase C (#963): uses explicit extern_specs parameter instead of EXTERN_SPECS thread-local.
    let extern_opt = if extern_specs.is_empty() {
        None
    } else {
        Some(extern_specs)
    };
    let path = tcx.def_path_str(def_id);
    let by_path = lookup_spec_with_extern(extern_opt, &path);
    if by_path.as_ref().is_some_and(spec_mutates_closure_state) {
        return true;
    }

    resolve_trait_method_def_id(tcx, def_id).is_some_and(|trait_method_id| {
        let trait_path = tcx.def_path_str(trait_method_id);
        lookup_spec_with_extern(extern_opt, &trait_path)
            .as_ref()
            .is_some_and(spec_mutates_closure_state)
    })
}

pub(super) fn mut_ref_local_for_operand(body: &Body<'_>, operand: &Operand<'_>) -> Option<Local> {
    let local = match operand {
        Operand::Move(place) | Operand::Copy(place) if place.projection.is_empty() => place.local,
        _ => return None,
    };
    let ty = body.local_decls[local].ty;
    matches!(
        ty.kind(),
        rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
    )
    .then_some(local)
}

pub(super) fn first_call_arg_is_mut_ref(body: &Body<'_>, args: &[Spanned<Operand<'_>>]) -> bool {
    let Some(local) = args
        .first()
        .and_then(|arg| mut_ref_local_for_operand(body, &arg.node))
    else {
        return false;
    };

    // `FnMut::call_mut` and `FnOnce::call_once` pass the closure receiver as
    // `&mut {closure...}` / `self`. Treat that separately from ordinary `&mut`
    // arguments so the dedicated closure-capture propagation path still runs.
    let rustc_middle::ty::TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Mut) =
        body.local_decls[local].ty.kind()
    else {
        return true;
    };

    !matches!(inner.kind(), rustc_middle::ty::TyKind::Closure(..))
}

pub(super) fn translated_mut_ref_arg_exprs_for_positions(
    _body: &Body<'_>,
    args: &[Spanned<Operand<'_>>],
    arg_positions: &[usize],
    local_exprs: &HashMap<Local, PureExpr>,
) -> Vec<PureExpr> {
    arg_positions
        .iter()
        .filter_map(|idx| args.get(*idx))
        // The mutating positions are already determined by the caller
        // (signature scan, spec metadata, or trusted builtin lowering).
        // Do not require the MIR operand itself to still be a plain `&mut`
        // local: wrappers like `ghost!(&mut **own)` lower through temporaries
        // whose Rust type no longer passes `mut_ref_local_for_operand`, even
        // though the translated argument expression still points at the
        // mutable state that must be advanced. (#permcell compat)
        .filter_map(|arg| translate_operand(&arg.node, local_exprs))
        .collect()
}

pub(super) fn propagate_mutating_ref_arg_states<'tcx>(
    local_exprs: &mut HashMap<Local, PureExpr>,
    body: &Body<'tcx>,
    arg_names: &[String],
    args: &[Spanned<Operand<'tcx>>],
    effects: Option<&mut CallEffects>,
    name_updates: Option<&mut HashMap<String, PureExpr>>,
) {
    let arg_positions = all_mut_ref_arg_positions(body, args);
    propagate_mutating_ref_arg_states_for_positions(
        local_exprs,
        body,
        arg_names,
        args,
        &arg_positions,
        effects,
        name_updates,
    );
}

pub(super) fn propagate_mutating_ref_arg_states_for_positions<'tcx>(
    local_exprs: &mut HashMap<Local, PureExpr>,
    body: &Body<'tcx>,
    arg_names: &[String],
    args: &[Spanned<Operand<'tcx>>],
    arg_positions: &[usize],
    mut effects: Option<&mut CallEffects>,
    mut name_updates: Option<&mut HashMap<String, PureExpr>>,
) {
    if !arg_positions.is_empty() {
        if let Some(effects) = effects.as_mut() {
            effects.has_mutating_call_effect = true;
        }
    }
    let arg_exprs =
        translated_mut_ref_arg_exprs_for_positions(body, args, arg_positions, local_exprs);
    for arg_expr in arg_exprs {
        propagate_mutating_receiver_state_with_captures(
            local_exprs,
            body,
            arg_names,
            &arg_expr,
            name_updates.as_deref_mut(),
        );
    }
}

pub(super) fn advance_mut_ref_deref_state_for_positions(
    body: &Body<'_>,
    args: &[Spanned<Operand<'_>>],
    arg_positions: &[usize],
    local_exprs: &HashMap<Local, PureExpr>,
    deref_exprs: &mut HashMap<Local, PureExpr>,
) {
    for arg in arg_positions.iter().filter_map(|idx| args.get(*idx)) {
        let Some(local) = mut_ref_local_for_operand(body, &arg.node) else {
            continue;
        };
        // Wrap the current local expression in Final() to represent the
        // post-call state. After chained mutating calls (#1597), local_exprs
        // may already contain Final-wrapped expressions (e.g., Final(Var("arr")))
        // — wrapping again produces the correct chaining depth.
        if let Some(expr) = local_exprs.get(&local) {
            let has_var_root = matches!(strip_receiver_state_wrappers(expr), PureExpr::Var(_, _));
            if has_var_root {
                deref_exprs.insert(local, PureExpr::Final(Arc::new(expr.clone())));
            }
        }
    }
}

pub(super) fn propagate_mutating_receiver_state(
    local_exprs: &mut HashMap<Local, PureExpr>,
    self_expr: &PureExpr,
) {
    let pre_state_expr = strip_receiver_state_wrappers(self_expr);
    let post_state_expr = final_receiver_state_expr(self_expr);
    let pre_state_name = match &pre_state_expr {
        PureExpr::Var(name, _) => Some(name.clone()),
        _ => None,
    };
    for expr in local_exprs.values_mut() {
        if *expr == pre_state_expr || *expr == *self_expr {
            *expr = post_state_expr.clone();
            continue;
        }
        if let Some(name) = pre_state_name.as_ref() {
            let rewritten = expr.rewrite_bottom_up(|node| match node {
                PureExpr::Var(var, sort) if var == *name => {
                    PureExpr::Final(Arc::new(PureExpr::Var(var, sort)))
                }
                // A `Deref(Var(name))` carrier denotes the SSA-stable CURRENT
                // pointee `name_current` (e.g. a frozen `snapshot!(*name)`).
                // Advancing the reference `name` to its prophecy does NOT change
                // its captured current value, so undo the inner rewrite the
                // bottom-up pass just applied and keep `Deref(Var(name))`. (#682)
                PureExpr::Deref(inner) => match inner.as_ref() {
                    PureExpr::Final(refinner)
                        if matches!(refinner.as_ref(), PureExpr::Var(var, _) if var == name) =>
                    {
                        PureExpr::Deref(refinner.clone())
                    }
                    _ => PureExpr::Deref(inner),
                },
                other => other,
            });
            *expr = rewritten;
        }
    }
}

pub(super) fn closure_capture_bindings(self_expr: &PureExpr) -> Vec<(usize, String)> {
    let base_expr = strip_receiver_state_wrappers(self_expr);
    let PureExpr::LogicFnCall { name, args } = base_expr else {
        return Vec::new();
    };

    if tuple_logic_fn_arity(&name) != Some(args.len()) {
        return Vec::new();
    }

    args.into_iter()
        .enumerate()
        .filter_map(|(idx, arg)| {
            let arg = strip_receiver_state_wrappers(&arg);
            match arg {
                PureExpr::Var(name, _) => Some((idx, name)),
                _ => None,
            }
        })
        .collect()
}

pub(super) fn propagate_mutating_receiver_state_with_captures<'tcx>(
    local_exprs: &mut HashMap<Local, PureExpr>,
    body: &Body<'tcx>,
    arg_names: &[String],
    self_expr: &PureExpr,
    mut name_updates: Option<&mut HashMap<String, PureExpr>>,
) {
    // When self_expr is Var(name) (e.g., from resolve_ref_to_named_local
    // preserving variable identity through reference chains), resolve it
    // to the structural tuple expression stored in local_exprs BEFORE
    // propagate_mutating_receiver_state runs. After that call, local_exprs
    // values get wrapped in Final() which destroys the structural info
    // needed by closure_capture_bindings. (#970)
    let resolved_self_expr;
    let stripped_self_expr = strip_receiver_state_wrappers(self_expr);
    let self_for_lookup = if matches!(stripped_self_expr, PureExpr::Var(_, _)) {
        &stripped_self_expr
    } else {
        self_expr
    };
    let effective_self = if closure_capture_bindings(self_expr).is_empty() {
        if let PureExpr::Var(name, _) = self_for_lookup {
            // Look up the local whose source name matches and whose value
            // is a structural tuple expression (closure env).
            resolved_self_expr = local_exprs
                .iter()
                .filter(|(local, expr)| {
                    source_name_for_local(body, **local, arg_names).as_deref()
                        == Some(name.as_str())
                        && !closure_capture_bindings(expr).is_empty()
                })
                .max_by_key(|(local, _)| local.as_u32())
                .map(|(_, expr)| expr.clone());
            resolved_self_expr.as_ref().unwrap_or(self_for_lookup)
        } else {
            self_expr
        }
    } else {
        self_expr
    };

    propagate_mutating_receiver_state(local_exprs, effective_self);

    let post_state_expr = final_receiver_state_expr(effective_self);
    let capture_bindings = closure_capture_bindings(effective_self);
    if capture_bindings.is_empty() {
        return;
    }

    let locals: Vec<Local> = local_exprs.keys().copied().collect();
    for (field_idx, capture_name) in capture_bindings {
        let projected = project_capture_field(&post_state_expr, field_idx);

        let target_local = locals
            .iter()
            .copied()
            .filter(|local| {
                source_name_for_local(body, *local, arg_names).as_deref() == Some(&capture_name)
            })
            .max_by_key(|local| local.as_u32());

        if let Some(local) = target_local {
            local_exprs.insert(local, projected.clone());
        }

        for expr in local_exprs.values_mut() {
            if matches!(expr, PureExpr::Var(name, _) if name == &capture_name) {
                *expr = projected.clone();
            }
        }

        // Only record name update when there is no local_exprs binding for
        // this capture name. `local_exprs` is already updated in this loop,
        // so build_name_substitutions will pick up the correct post-call value
        // via best_for_name. Adding a redundant name_update triggers the
        // self-reference resolver which double-wraps Final() (#1489).
        if let Some(updates) = name_updates.as_mut() {
            let has_local_binding = target_local.is_some();
            if !has_local_binding {
                updates.insert(capture_name, projected);
            }
        }
    }
}
