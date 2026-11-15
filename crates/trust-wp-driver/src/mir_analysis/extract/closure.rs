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

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{Body, Local, Operand},
    ty::TyCtxt,
};
use rustc_span::Spanned;
use trust_wp_core::formula::{
    internal::tuple_lowering::{
        tuple_field_logic_fn_index, tuple_logic_fn_arity, tuple_logic_fn_name,
    },
    ExprSort, PureExpr,
};
use trust_wp_driver::StdSpec;

use super::{helpers::source_name_for_local, SubstitutionExtractionContext};
pub(super) use crate::callbacks::{final_receiver_state_expr, projected_capture_post_state};
use crate::{
    callbacks::strip_receiver_state_wrappers,
    mir_analysis::{
        call_resolve::{extract_call_def_id, resolve_trait_method_def_id},
        effects::CallEffects,
        spec_apply::TranslatedArg,
        translate::{translate_operand, translate_operand_with_tcx},
    },
};

mod mut_ref_spec;
mod postcondition_substitution;
mod untuple;

pub(crate) use mut_ref_spec::ty_exposes_interior_mutability;
pub(super) use mut_ref_spec::{
    all_mut_ref_arg_positions, call_result_for_interior_mutable_args, callee_forwards_mut_borrow,
    havoc_interior_capability_roots, interior_capability_roots,
    nested_interior_capability_arg_positions, resolved_call_mutating_ref_arg_positions,
    spec_mutates_closure_state, spec_mutating_ref_arg_positions,
    union_interior_mutable_write_positions,
};
#[cfg(test)]
pub(super) use mut_ref_spec::{
    path_forwards_mut_borrow, spec_clause_aliases_for_arg_index,
    spec_mentions_post_state_for_aliases, spec_result_carries_arg_reference,
    FORWARDING_SHARED_PROJECTION_TRAIT_PATHS, FORWARDING_SPEC_LIBRARY_SUFFIXES,
    FORWARDING_STD_CALLEES, MUT_REBORROW_PROJECTION_PATHS_KNOWN_UNSOUND,
};
pub(super) use postcondition_substitution::{
    project_capture_field, substitute_capture_fields_in_postcondition,
};
pub(super) use untuple::untupled_closure_call_args;

/// Secondary (substitution-pass) twin of [`resolve_closed_thunk_closure_args`].
///
/// A closure argument never stands in for the result of calling it unless the
/// value is exact by construction; this delegates to the single exact-thunk
/// rule so both pipelines agree. (#1277)
pub(super) fn resolve_closure_arg_return_values<'tcx>(
    ctx: &SubstitutionExtractionContext<'_, 'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    translated_args: &mut [TranslatedArg],
) {
    resolve_closed_thunk_closure_args(
        ctx.tcx,
        body,
        args,
        translated_args,
        ctx.user_specs,
        ctx.trait_specs,
        ctx.extern_specs,
    );
}

/// Replace a closure argument by the value every call to it returns — ONLY
/// when that value is exact by construction:
///
/// - the argument's type is a real closure with no captures, no parameters and
///   no user contract (a `#[requires]` on the closure must never be bypassed);
/// - its optimized MIR body has the shape accepted by
///   [`exact_thunk_value_from_shape`]: a straight `Goto` chain (no back edges,
///   no calls, no asserts, no switches, no unreachable/diverging terminators)
///   whose only non-storage statement is exactly one assignment of an
///   evaluated literal constant to the return place.
///
/// Anything else keeps its translated expression WITHOUT the exact flag, so a
/// contract clause that applies the corresponding parameter is dropped by
/// `spec_apply` instead of being substituted. (option.rs `ok_or_else`)
pub(super) fn resolve_closed_thunk_closure_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    translated_args: &mut [TranslatedArg],
    user_specs: &HashMap<DefId, StdSpec>,
    _trait_specs: &HashMap<DefId, StdSpec>,
    _extern_specs: &HashMap<String, StdSpec>,
) {
    for (idx, arg) in args.iter().enumerate() {
        if translated_args.get(idx).is_none() {
            continue;
        }
        // Borrowck MIR passes the closure by place; optimized MIR passes a
        // capture-free closure as a zero-sized constant of the closure type.
        let arg_ty = match &arg.node {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                body.local_decls[place.local].ty
            }
            Operand::Constant(constant) => constant.ty(),
            _ => continue,
        };
        let rustc_middle::ty::TyKind::Closure(closure_def_id, closure_args) = arg_ty.kind() else {
            continue;
        };
        if !matches!(tcx.def_kind(*closure_def_id), DefKind::Closure) {
            continue;
        }
        if user_specs.contains_key(closure_def_id) {
            continue;
        }
        let closure_args = closure_args.as_closure();
        if closure_args.upvar_tys().iter().next().is_some() {
            continue;
        }
        let sig = closure_args.sig().skip_binder();
        let no_params = match sig.inputs() {
            [] => true,
            [tupled] => tupled.tuple_fields().is_empty(),
            _ => false,
        };
        if !no_params || !tcx.is_mir_available(*closure_def_id) {
            continue;
        }
        let closure_body = tcx.optimized_mir(*closure_def_id);
        let shape = thunk_body_shape(tcx, closure_body);
        if let Some(value) = exact_thunk_value_from_shape(&shape) {
            translated_args[idx] = TranslatedArg::exact_thunk_value(value);
        }
    }
}

/// Abstract statement shape of a candidate thunk body.
#[derive(Clone, Debug)]
pub(super) enum ThunkStmtShape {
    /// `StorageLive` / `StorageDead` / `Nop`: no observable effect.
    Inert,
    /// `_0 = const C` with `C` an evaluated constant; `None` when it does not
    /// translate to an exact literal.
    ReturnConst(Option<PureExpr>),
    /// Anything else: borrows, writes through projections, other rvalues.
    Other,
}

/// Abstract terminator shape of a candidate thunk body.
#[derive(Clone, Debug)]
pub(super) enum ThunkTermShape {
    Goto(usize),
    Return,
    /// Calls, asserts, switches, drops, unreachable, false edges/unwinds, ...
    Other,
}

fn thunk_body_shape<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<(Vec<ThunkStmtShape>, ThunkTermShape)> {
    use rustc_middle::mir::{Const as MirConst, Rvalue, StatementKind, TerminatorKind};

    body.basic_blocks
        .iter()
        .map(|block| {
            let stmts = block
                .statements
                .iter()
                .map(|stmt| match &stmt.kind {
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Nop => ThunkStmtShape::Inert,
                    StatementKind::Assign(assign) => {
                        let (place, rvalue) = &**assign;
                        match rvalue {
                            Rvalue::Use(Operand::Constant(constant), _)
                                if place.local == rustc_middle::mir::RETURN_PLACE
                                    && place.projection.is_empty()
                                    && !matches!(constant.const_, MirConst::Unevaluated(..)) =>
                            {
                                let empty: HashMap<Local, PureExpr> = HashMap::new();
                                ThunkStmtShape::ReturnConst(translate_operand_with_tcx(
                                    &Operand::Constant(constant.clone()),
                                    &empty,
                                    tcx,
                                ))
                            }
                            _ => ThunkStmtShape::Other,
                        }
                    }
                    _ => ThunkStmtShape::Other,
                })
                .collect();
            let term = match block.terminator.as_ref().map(|t| &t.kind) {
                Some(TerminatorKind::Goto { target, .. }) => {
                    ThunkTermShape::Goto(target.as_usize())
                }
                Some(TerminatorKind::Return) => ThunkTermShape::Return,
                _ => ThunkTermShape::Other,
            };
            (stmts, term)
        })
        .collect()
}

/// The exact value a thunk body returns, or `None` when the shape is not
/// exact by construction.
///
/// Walks the control path from the entry block. Every block on it must end in
/// `Goto` or `Return`; revisiting a block (a back edge) rejects; any `Other`
/// statement or terminator rejects; the return place must be assigned exactly
/// once, from a constant that translated to an integer or boolean literal.
pub(super) fn exact_thunk_value_from_shape(
    blocks: &[(Vec<ThunkStmtShape>, ThunkTermShape)],
) -> Option<PureExpr> {
    let mut visited = vec![false; blocks.len()];
    let mut current = 0usize;
    let mut value: Option<PureExpr> = None;
    let mut assignments = 0usize;
    loop {
        let (stmts, term) = blocks.get(current)?;
        if std::mem::replace(&mut visited[current], true) {
            return None;
        }
        for stmt in stmts {
            match stmt {
                ThunkStmtShape::Inert => {}
                ThunkStmtShape::ReturnConst(Some(lit @ (PureExpr::Int(_) | PureExpr::Bool(_)))) => {
                    assignments += 1;
                    value = Some(lit.clone());
                }
                ThunkStmtShape::ReturnConst(_) | ThunkStmtShape::Other => return None,
            }
        }
        match term {
            ThunkTermShape::Goto(target) => current = *target,
            ThunkTermShape::Return => {
                return (assignments == 1).then_some(value).flatten();
            }
            ThunkTermShape::Other => return None,
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
                // The capture is named as the parent's binding is (D-237).
                return crate::mir_analysis::binding_identity::hir_binding_debug_name(
                    tcx,
                    &var_ident_name,
                    capture.get_root_variable(),
                );
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

    // Extern specs arrive as an explicit parameter; there is no thread-local fallback.
    let extern_opt = if extern_specs.is_empty() {
        None
    } else {
        Some(extern_specs)
    };
    let path = tcx.def_path_str(def_id);
    // Mutation DETECTION: a spec that mutates makes the caller more
    // conservative (captures get prophecy carriers), so builtin specs are
    // consulted without call-site admission here; nothing is granted.
    let admission = crate::provenance::BuiltinSpecAdmission::Admitted;
    let by_path =
        crate::provenance::lookup_spec_for_def(tcx, def_id, admission, extern_opt, &path, None);
    if by_path.as_ref().is_some_and(spec_mutates_closure_state) {
        return true;
    }

    resolve_trait_method_def_id(tcx, def_id).is_some_and(|trait_method_id| {
        let trait_path = tcx.def_path_str(trait_method_id);
        crate::provenance::lookup_spec_for_def(
            tcx,
            trait_method_id,
            admission,
            extern_opt,
            &trait_path,
            None,
        )
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
    // Translate every argument against the PRE-call state before any
    // propagation. The mutating positions are already determined by the
    // caller (signature scan, spec metadata, or trusted builtin lowering), so
    // the MIR operand itself need not still be a plain `&mut` local: wrappers
    // like `ghost!(&mut **own)` lower through temporaries whose Rust type no
    // longer passes `mut_ref_local_for_operand`. (#permcell compat)
    let arg_exprs: Vec<(&Operand<'tcx>, PureExpr)> = arg_positions
        .iter()
        .filter_map(|idx| args.get(*idx))
        .filter_map(|arg| translate_operand(&arg.node, local_exprs).map(|expr| (&arg.node, expr)))
        .collect();
    for (operand, arg_expr) in arg_exprs {
        propagate_mutating_receiver_state_with_captures(
            local_exprs,
            body,
            arg_names,
            &arg_expr,
            Some(operand),
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
        // post-call state. After chained mutating calls, local_exprs
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
    propagate_mutating_receiver_state_except(local_exprs, self_expr, &HashSet::new());
}

/// Advance the receiver's state to its post-call prophecy in every local that
/// denotes (or is built from) the receiver place, EXCEPT the `frozen` locals.
///
/// A frozen local holds a VALUE fixed at its assignment (see
/// [`receiver_mutation_frozen_locals`]); a later mutation of the receiver
/// through `&mut` cannot change it, so rewriting its expression to mention
/// `Final(receiver)` would rebind a copy to the post-call state
/// (`let n = v.len(); v.push(1)` would bind `n` to the post-push length;
/// `s31_len_read_frozen_after_push`).
pub(super) fn propagate_mutating_receiver_state_except(
    local_exprs: &mut HashMap<Local, PureExpr>,
    self_expr: &PureExpr,
    frozen: &HashSet<Local>,
) {
    let pre_state_expr = strip_receiver_state_wrappers(self_expr);
    let post_state_expr = final_receiver_state_expr(self_expr);
    let pre_state_name = match &pre_state_expr {
        PureExpr::Var(name, _) => Some(name.clone()),
        _ => None,
    };
    for (local, expr) in local_exprs.iter_mut() {
        if frozen.contains(local) {
            continue;
        }
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

/// The captures a call of the closure `closure_def_id` substitutes into the
/// closure's clauses: capture `N` under every name the closure's own contract
/// lane reads as `self.N` (`closure_capture_index_names`), so the call owes the
/// precondition that lane assumes. Those come first, and the substitution takes
/// the first binding a name matches; the names [`closure_capture_bindings`]
/// reads off the caller's value for each capture follow.
///
/// Read off the value alone, a capture whose value is not a bare variable (the
/// constant `1` of `let x = 1;`, the `a + 1` of `let y = a + 1;`) is bound by
/// no name, and the clause is owed over a name nothing binds.
pub(super) fn closure_call_capture_bindings(
    tcx: TyCtxt<'_>,
    closure_def_id: DefId,
    self_expr: &PureExpr,
) -> Vec<(usize, String)> {
    let by_value = closure_capture_bindings(self_expr);
    let Some(local_def_id) = closure_def_id.as_local() else {
        return by_value;
    };
    if tcx.def_kind(closure_def_id) != DefKind::Closure {
        return by_value;
    }
    let PureExpr::LogicFnCall { name, args } = strip_receiver_state_wrappers(self_expr) else {
        return by_value;
    };
    let captures = tcx.closure_captures(local_def_id).len();
    if tuple_logic_fn_arity(&name) != Some(args.len()) || args.len() != captures {
        return by_value;
    }
    let mut bindings = crate::callbacks::closure_capture_index_names(tcx, local_def_id);
    bindings.extend(by_value);
    bindings
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
    receiver_operand: Option<&Operand<'tcx>>,
    name_updates: Option<&mut HashMap<String, PureExpr>>,
) {
    // A `Snapshot<T>` local holds a value FROZEN at its capture point
    // (`snapshot!(v)` = `Snapshot::capture(&v)`). The receiver-state rewrite
    // below advances every local whose expression equals (or mentions) the
    // receiver's pre-state to the post-call prophecy, so `old = snapshot!(v);
    // v.push(1)` would rebind `old` to `Final(v)` and `proof_assert!(v@ == old@)`
    // would reduce to `true` (false accept). Mutating `v` never changes a
    // snapshot: restore every snapshot-typed local's expression after the
    // rewrite (`s25_snapshot_frozen_after_mutation`).
    let frozen_snapshots: Vec<(Local, PureExpr)> = local_exprs
        .iter()
        .filter(|(local, _)| local_is_snapshot_value(body, **local))
        .map(|(local, expr)| (*local, expr.clone()))
        .collect();
    // A mutation through a borrow of a FIELD of a by-value local (`w.0.push(7)`
    // is `_3 = &mut _1.0; Vec::push(move _3, 7)`) must reach the owner's whole
    // value: the rewrite below only advances expressions that mention the
    // receiver's pre-state, and an owner bound to an opaque symbol (a
    // parameter's `Var(w)`) does not mention `tuple_get_0(w)`. An owner left
    // unchanged would keep its PRE-call value (false accept: `fn f(mut w: W)
    // -> W { w.0.push(7); w }` with `result.0@.len() == w.0@.len()`); rebind it
    // to a fresh unconstrained symbol instead (fail-closed;
    // `s34_byval_vec_newtype_push`).
    let field_owner = receiver_operand.and_then(|operand| field_borrow_owner(body, operand));
    // The proof_assert substitution lane (the only caller passing
    // `name_updates`) asserts each binding as a fact over the source symbol;
    // the extraction lane binds program-point values. See the owner havoc.
    let substitution_lane = name_updates.is_some();
    let owner_before = field_owner.and_then(|owner| local_exprs.get(&owner).cloned());
    // Value copies taken before the call (`let n = p.a;`), for the owner-havoc
    // case below. See the restore after the havoc.
    let pre_call_value_copies: Vec<(Local, PureExpr)> = match field_owner {
        Some(owner) => {
            let owner_name = source_name_for_local(body, owner, arg_names);
            let mutated_places = receiver_operand
                .and_then(|operand| mutated_place_locals(body, operand))
                .unwrap_or_default();
            local_exprs
                .iter()
                .filter(|(local, _)| {
                    **local != owner
                        && !mutated_places.contains(*local)
                        && !local_type_may_hold_borrow(body, **local)
                        && (owner_name.is_none()
                            || source_name_for_local(body, **local, arg_names) != owner_name)
                })
                .map(|(local, expr)| (*local, expr.clone()))
                .collect()
        }
        None => Vec::new(),
    };
    propagate_mutating_receiver_state_with_captures_inner(
        local_exprs,
        body,
        arg_names,
        self_expr,
        receiver_operand,
        name_updates,
    );
    for (local, expr) in frozen_snapshots {
        local_exprs.insert(local, expr);
    }
    if let (Some(owner), Some(before)) = (field_owner, owner_before) {
        if local_exprs.get(&owner) == Some(&before) {
            let sort = match &before {
                PureExpr::Var(_, sort) => sort.clone(),
                _ => None,
            };
            // In the proof_assert substitution lane, an owner bound to its own
            // source symbol (a by-value parameter's `Var(p)`) advances to the
            // post-state `Final(Var(p))`, the same
            // form a whole-value `&mut p` argument advances to. A fresh
            // unrelated symbol is WRONG there: the proof_assert lane asserts
            // each substitution as a fact `p == <value at cutoff>` over the
            // very symbol `p` that pre-call copies (`let n = p.a`) are
            // expressed in, so `p == $havoc` would equate the post-call owner
            // with its entry value and frame `p.a`
            // (`s48_uncontracted_helper_param_field_scalar`).
            // Only in the substitution lane: there the owner's fresh symbol
            // would be tied back to its entry value (below). In the
            // extraction lane a fresh symbol IS the unknown post-state, and
            // `Final(Var(w))` over a by-value parameter would collapse to
            // `w` (s34_byval_vec_named_push).
            let advanced = match &before {
                PureExpr::Var(name, _)
                    if substitution_lane
                        && source_name_for_local(body, owner, arg_names).as_deref()
                            == Some(name.as_str()) =>
                {
                    PureExpr::Final(Arc::new(before.clone()))
                }
                _ => {
                    let serial =
                        FIELD_OWNER_HAVOC_SERIAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    PureExpr::Var(format!("$havoc_owner_{}_{serial}", owner.as_u32()), sort)
                }
            };
            local_exprs.insert(owner, advanced);
            // The owner denotes a fresh post-call value from here on, so a
            // copy taken before the call must keep its PRE-call value. The
            // mention rewrite above advances any copy whose expression equals
            // the field read (`let n = p.a` becomes `Final(p.a)`), which for a
            // by-value PARAMETER (whose copies the freeze deliberately skips)
            // would disconnect `n` from the entry value and let `n@ == p.a@`
            // verify after `set7(&mut p.a)`. A non-borrow local holds a value
            // fixed at its assignment; a write through a borrow of the owner's
            // field cannot change it. Restoring it is Rust semantics, and the
            // owner (the only place the call can change) stays havocked
            // (`s48_uncontracted_helper_param_field_scalar`).
            for (local, expr) in pre_call_value_copies {
                if local_exprs.contains_key(&local) {
                    local_exprs.insert(local, expr);
                }
            }
        }
    }
}

/// Distinguishes the fresh symbols of successive owner havocs (each mutating
/// call yields a DIFFERENT unknown post-state).
static FIELD_OWNER_HAVOC_SERIAL: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// The by-value local whose field path `operand` mutably borrows: `operand` is
/// a plain local assigned exactly once, from `&mut owner.f1..fk` (k >= 1, no
/// deref) or from a reborrow `&mut *m` of such a local. `None` otherwise.
fn field_borrow_owner(body: &Body<'_>, operand: &Operand<'_>) -> Option<Local> {
    use rustc_middle::mir::{BorrowKind, ProjectionElem, Rvalue, StatementKind};
    let (Operand::Move(place) | Operand::Copy(place)) = operand else {
        return None;
    };
    if !place.projection.is_empty() {
        return None;
    }
    let mut local = place.local;
    for _ in 0..8 {
        let mut sources = body
            .basic_blocks
            .iter()
            .flat_map(|block| &block.statements)
            .filter_map(|statement| match &statement.kind {
                StatementKind::Assign((dest, rvalue)) if dest.local == local => {
                    Some((dest.projection.is_empty(), rvalue))
                }
                _ => None,
            });
        let (whole, rvalue) = sources.next()?;
        if !whole || sources.next().is_some() {
            return None;
        }
        let Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed) = rvalue else {
            return None;
        };
        let projections = borrowed.projection.as_ref();
        match projections {
            [ProjectionElem::Deref] => local = borrowed.local,
            [] => return None,
            _ if projections
                .iter()
                .all(|projection| matches!(projection, ProjectionElem::Field(..))) =>
            {
                return (!(1..=body.arg_count).contains(&borrowed.local.as_usize())
                    || !matches!(
                        body.local_decls[borrowed.local].ty.kind(),
                        rustc_middle::ty::TyKind::Ref(..)
                    ))
                .then_some(borrowed.local);
            }
            _ => return None,
        }
    }
    None
}

/// The locals a mutating call through `receiver_operand` CANNOT change; empty
/// when the mutated place cannot be located in the MIR (then nothing is frozen
/// and the caller advances every local, `propagate_mutating_receiver_state`).
///
/// A local is frozen when its declared type can hold no borrow
/// ([`local_type_may_hold_borrow`] is false) and it is not one of the
/// [`mutated_place_locals`] of the receiver (nor shares a source name with
/// one). Soundness: in safe Rust a mutation through `&mut P` changes only the
/// place `P` and what is reachable from locals holding a borrow into it; a
/// local whose type has no region, raw pointer, closure, coroutine, trait
/// object or opaque type cannot hold such a borrow, so its value is the one
/// assigned to it. The place is identified from the MIR, NOT from the
/// receiver expression: `let mut y = x; inc(&mut y)` translates the receiver
/// to `Var(x)` (`resolve_ref_to_named_local` preserves value identity), and a
/// name-based exclusion would freeze the mutated `y` at its pre-call value.
/// (#mutrecv-copies)
pub(super) fn receiver_mutation_frozen_locals(
    local_exprs: &HashMap<Local, PureExpr>,
    body: &Body<'_>,
    arg_names: &[String],
    receiver_operand: Option<&Operand<'_>>,
) -> HashSet<Local> {
    let Some(places) = receiver_operand.and_then(|operand| mutated_place_locals(body, operand))
    else {
        return HashSet::new();
    };
    // A place rooted at a function argument carries no tracked post-state in
    // `local_exprs` (a later read of the parameter does not see the call's
    // prophecy), so freezing its copies would make `let n = v.len();
    // v.push(1); proof_assert!(n@ == v@.len())` compare two stale reads.
    // Freeze nothing there. (#mutrecv-copies)
    if places
        .iter()
        .any(|local| (1..=body.arg_count).contains(&local.as_usize()))
    {
        return HashSet::new();
    }
    let place_names: HashSet<String> = places
        .iter()
        .filter_map(|local| source_name_for_local(body, *local, arg_names))
        .collect();
    local_exprs
        .keys()
        .copied()
        .filter(|local| {
            !places.contains(local)
                && !local_type_may_hold_borrow(body, *local)
                && !source_name_for_local(body, *local, arg_names)
                    .is_some_and(|name| place_names.contains(&name))
        })
        .collect()
}

/// Collect the MIR locals that are, own, or borrow into the place a call
/// mutates through `operand`. Starting from the operand's local, every
/// borrow-bearing local is followed back through the assignments whose place
/// IS that local (the places it borrows/reborrows/copies from, and every
/// argument of a call that returned it — a returned borrow can only derive
/// from the call's inputs or from a place that is no local of this body). A
/// local that cannot hold a borrow is the owning place itself and is not
/// followed further (`let mut w = v; w.push(1)` mutates `w`, not `v`).
/// Returns `None` for a constant operand or an assignment shape this walk does
/// not model, so callers fall back to freezing nothing.
///
/// NOT an over-approximation: a borrow local reseated through an indirect
/// write (`let rr = &mut r; *rr = &mut b;`) or through a call that takes
/// `&mut r` is not followed, because only direct assignments to the local are
/// read. Such programs are a known false accept independent of the copy
/// freeze (a reseat through `*rr = &mut b` or through a call taking `&mut r`
/// redirects the write to `b` while the walk still attributes it to `r`); the
/// freeze does not make them worse, but its soundness must not be argued from
/// this set being complete.
pub(super) fn mutated_place_locals(
    body: &Body<'_>,
    operand: &Operand<'_>,
) -> Option<HashSet<Local>> {
    use rustc_middle::mir::{Rvalue, StatementKind, TerminatorKind};
    let start = match operand {
        Operand::Move(place) | Operand::Copy(place) => place.local,
        _ => return None,
    };
    fn push_operand(operand: &Operand<'_>, work: &mut Vec<Local>) {
        if let Operand::Move(place) | Operand::Copy(place) = operand {
            work.push(place.local);
        }
    }
    let mut out = HashSet::new();
    let mut work = vec![start];
    while let Some(local) = work.pop() {
        if !out.insert(local) {
            continue;
        }
        if !local_type_may_hold_borrow(body, local) {
            continue;
        }
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let StatementKind::Assign((place, rvalue)) = &statement.kind else {
                    continue;
                };
                if place.local != local || place.is_indirect() {
                    continue;
                }
                match rvalue {
                    Rvalue::Ref(_, _, source)
                    | Rvalue::RawPtr(_, source)
                    | Rvalue::CopyForDeref(source) => work.push(source.local),
                    Rvalue::Use(op, _)
                    | Rvalue::Cast(_, op, _)
                    | Rvalue::UnaryOp(_, op)
                    | Rvalue::Repeat(op, _) => push_operand(op, &mut work),
                    Rvalue::BinaryOp(_, (lhs, rhs)) => {
                        push_operand(lhs, &mut work);
                        push_operand(rhs, &mut work);
                    }
                    Rvalue::Aggregate(_, operands) => {
                        for op in operands {
                            push_operand(op, &mut work);
                        }
                    }
                    _ => return None,
                }
            }
            if let Some(terminator) = &block.terminator {
                if let TerminatorKind::Call {
                    destination, args, ..
                } = &terminator.kind
                {
                    if destination.local == local {
                        for arg in args.iter() {
                            push_operand(&arg.node, &mut work);
                        }
                    }
                }
            }
        }
    }
    Some(out)
}

/// Whether the declared type of `local` may hold a borrow of another place:
/// any region anywhere in the type (including erased ones — `&mut T`,
/// `Ghost<&mut T>`, `Foo<'a>`), a raw pointer, a closure or coroutine
/// environment (by-ref captures), a trait object, or an alias type (an opaque
/// type may capture borrows; projections are treated the same way). An unknown local is conservatively borrow-bearing.
///
/// Type parameters without regions are NOT borrow-bearing:
/// a value of such a type in this body cannot hold a borrow created in this
/// body (its type would have to name that borrow's region), and a borrow of a
/// caller place it could hold is not the receiver, which is uniquely borrowed
/// for the call. Raw pointers hidden in a region-free ADT's private fields
/// (`Vec<T>`) are not followed: reaching a place through them is unsafe code.
pub(super) fn local_type_may_hold_borrow(body: &Body<'_>, local: Local) -> bool {
    use rustc_middle::ty::{GenericArgKind, TyKind};
    let Some(decl) = body.local_decls.get(local) else {
        return true;
    };
    decl.ty.walk().any(|arg| match arg.kind() {
        GenericArgKind::Lifetime(_) => true,
        GenericArgKind::Type(ty) => matches!(
            ty.kind(),
            TyKind::Ref(..)
                | TyKind::RawPtr(..)
                | TyKind::Closure(..)
                | TyKind::CoroutineClosure(..)
                | TyKind::Coroutine(..)
                | TyKind::CoroutineWitness(..)
                | TyKind::Dynamic(..)
                | TyKind::Alias(..)
        ),
        GenericArgKind::Const(_) => false,
    })
}

/// Whether `local` has type `Snapshot<_>` (creusot_std / trust_wp_std /
/// creusot_contracts ghost snapshot). Its logical value is immutable.
fn local_is_snapshot_value(body: &Body<'_>, local: Local) -> bool {
    let Some(decl) = body.local_decls.get(local) else {
        return false;
    };
    let rustc_middle::ty::TyKind::Adt(adt, _) = decl.ty.kind() else {
        return false;
    };
    let did = adt.did();
    rustc_middle::ty::tls::with_opt(|tcx| {
        tcx.is_some_and(|tcx| {
            let crate_name = tcx.crate_name(did.krate).to_string();
            matches!(
                crate_name.as_str(),
                "trust_wp_std" | "creusot_std" | "creusot_contracts" | "trust_wp"
            ) && tcx.item_name(did).as_str() == "Snapshot"
        })
    })
}

fn propagate_mutating_receiver_state_with_captures_inner<'tcx>(
    local_exprs: &mut HashMap<Local, PureExpr>,
    body: &Body<'tcx>,
    arg_names: &[String],
    self_expr: &PureExpr,
    receiver_operand: Option<&Operand<'tcx>>,
    mut name_updates: Option<&mut HashMap<String, PureExpr>>,
) {
    // When self_expr is Var(name) (e.g., from resolve_ref_to_named_local
    // preserving variable identity through reference chains), resolve it
    // to the structural tuple expression stored in local_exprs BEFORE
    // propagate_mutating_receiver_state runs. After that call, local_exprs
    // values get wrapped in Final() which destroys the structural info
    // needed by closure_capture_bindings.
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

    // Freeze value copies ONLY around the mention/equality rewrite: the
    // capture-binding loop below and `apply_chain_advancement` (Phase B, run
    // by the callers) still write the captured variables and borrow-chain
    // bases.
    //
    // The freeze is committed only when a NAMED place local present in
    // `local_exprs` really advances to the post-call state: otherwise the
    // mutation's effect lives only in the (old) rewrite of the copies, and a
    // frozen copy would compare equal to an equally stale read of the place.
    let mut frozen =
        receiver_mutation_frozen_locals(local_exprs, body, arg_names, receiver_operand);
    if frozen.is_empty() {
        propagate_mutating_receiver_state(local_exprs, effective_self);
    } else {
        let named_places: Vec<Local> = receiver_operand
            .and_then(|operand| mutated_place_locals(body, operand))
            .into_iter()
            .flatten()
            .filter(|local| source_name_for_local(body, *local, arg_names).is_some())
            .collect();
        let mut trial = local_exprs.clone();
        propagate_mutating_receiver_state_except(&mut trial, effective_self, &frozen);
        let place_advanced = named_places.iter().any(|local| {
            local_exprs.contains_key(local) && trial.get(local) != local_exprs.get(local)
        });
        if place_advanced {
            *local_exprs = trial;
        } else {
            frozen.clear();
            propagate_mutating_receiver_state(local_exprs, effective_self);
        }
    }

    let post_state_expr = final_receiver_state_expr(effective_self);
    let capture_bindings = closure_capture_bindings(effective_self);
    // A capture of a FIELD (`|| { p.0 = 9 }`) is not a local of its own: the
    // environment slot holds the owner's projection, so `capture_bindings` —
    // which only names whole-variable captures — sees nothing and the owner
    // keeps the entry symbol the caller's `#[requires]` constrains. The write
    // the closure performed is then not merely forgotten but contradicted.
    // Collect each such owner's post-state FIELD-WISE; a whole-owner advance
    // is wrong the other way, forgetting fields the closure never captured.
    let mut projected_owner_fields: HashMap<String, HashMap<usize, PureExpr>> = HashMap::new();
    for (owner_name, owner_field, sort) in projected_capture_owner_fields(effective_self) {
        let post = projected_capture_post_state(&owner_name, owner_field, sort);
        projected_owner_fields
            .entry(owner_name)
            .or_default()
            .insert(owner_field, post);
    }
    if capture_bindings.is_empty() {
        rebind_projected_capture_owners(
            local_exprs,
            body,
            arg_names,
            &projected_owner_fields,
            name_updates,
        );
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

        for (local, expr) in local_exprs.iter_mut() {
            // A frozen COPY of the captured variable (`let y = x; c()`) keeps
            // its value; the variable's own locals (same source name) are the
            // captured place and must advance. (#mutrecv-copies)
            if frozen.contains(local)
                && source_name_for_local(body, *local, arg_names).as_deref()
                    != Some(capture_name.as_str())
            {
                continue;
            }
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

    rebind_projected_capture_owners(
        local_exprs,
        body,
        arg_names,
        &projected_owner_fields,
        name_updates,
    );
}

/// The post-call value of each tuple-projected capture of a caller local, as
/// `(owner, owner field, value)`.
///
/// The one producer of that value: the place's advance and the closure
/// postcondition's credit must name the same carrier, and they are computed in
/// two different passes.
pub(super) fn projected_capture_post_states(
    self_expr: &PureExpr,
) -> Vec<(String, usize, PureExpr)> {
    projected_capture_owner_fields(self_expr)
        .into_iter()
        .map(|(owner, field, sort)| {
            let post = projected_capture_post_state(&owner, field, sort);
            (owner, field, post)
        })
        .collect()
}

/// Re-attribute a closure postcondition to the capture's post-call value.
///
/// A closure's own `#[ensures]` names a captured field by the OWNER's source
/// name (`p.1`), and at the caller that name is the owner's ENTRY symbol — the
/// very symbol the caller's `#[requires]` constrains. Crediting the closure's
/// clause there makes one symbol carry two states at once. `old(p.1)` keeps
/// naming the entry value, which is what it means.
pub(super) fn attribute_capture_credit(
    expr: &PureExpr,
    post_states: &[(String, usize, PureExpr)],
) -> PureExpr {
    expr.rewrite_bottom_up_prune(
        |node| !matches!(node, PureExpr::Old(_)),
        |node| {
            let PureExpr::LogicFnCall { ref name, ref args } = node else {
                return node;
            };
            let Some(field_idx) = tuple_field_logic_fn_index(name) else {
                return node;
            };
            let [PureExpr::Var(owner_name, _)] = args.as_slice() else {
                return node;
            };
            post_states
                .iter()
                .find(|(owner, field, _)| owner == owner_name && *field == field_idx)
                .map_or_else(|| node.clone(), |(_, _, post)| post.clone())
        },
    )
}

/// For an environment whose slots hold FIELDS of a caller local
/// (`__trust_wp_tuple2(tuple_get_0(p), tuple_get_1(p))`), the
/// `(owner name, owner field, owner sort)` triples it projects.
///
/// A slot that is not a field projection of a named local belongs to the
/// whole-variable capture lane and is left to it.
fn projected_capture_owner_fields(self_expr: &PureExpr) -> Vec<(String, usize, Option<ExprSort>)> {
    let PureExpr::LogicFnCall { name, args } = strip_receiver_state_wrappers(self_expr) else {
        return Vec::new();
    };
    if tuple_logic_fn_arity(&name) != Some(args.len()) {
        return Vec::new();
    }
    args.into_iter()
        .filter_map(|arg| {
            let PureExpr::LogicFnCall { name, args } = strip_receiver_state_wrappers(&arg) else {
                return None;
            };
            let field_idx = tuple_field_logic_fn_index(&name)?;
            let [owner] = args.as_slice() else {
                return None;
            };
            match strip_receiver_state_wrappers(owner) {
                PureExpr::Var(owner_name, sort) => Some((owner_name, field_idx, sort)),
                _ => None,
            }
        })
        .collect()
}

/// Rebind each owner of a tuple-projected `&mut` capture to its post-call
/// value: every captured field takes the closure environment's post-state
/// projection, every other field keeps the value it entered with.
///
/// When no term denotes the owner field-wise — the owner is not a tuple, or a
/// captured index is out of range — the owner is havocked. The one shape that
/// must never survive is leaving it bound to its entry symbol: the caller's
/// entry premise would then still describe a place the closure wrote.
fn rebind_projected_capture_owners<'tcx>(
    local_exprs: &mut HashMap<Local, PureExpr>,
    body: &Body<'tcx>,
    arg_names: &[String],
    projected_owner_fields: &HashMap<String, HashMap<usize, PureExpr>>,
    mut name_updates: Option<&mut HashMap<String, PureExpr>>,
) {
    for (owner_name, fields) in projected_owner_fields {
        let Some(owner_local) = body
            .local_decls
            .indices()
            .filter(|local| {
                source_name_for_local(body, *local, arg_names).as_deref()
                    == Some(owner_name.as_str())
            })
            .max_by_key(|local| local.as_u32())
        else {
            continue;
        };
        let arity = match body.local_decls[owner_local].ty.kind() {
            rustc_middle::ty::TyKind::Tuple(elems) => Some(elems.len()),
            _ => None,
        };
        let base = local_exprs
            .get(&owner_local)
            .cloned()
            .unwrap_or_else(|| PureExpr::Var(owner_name.clone(), None));
        let havoc = || {
            let serial =
                FIELD_OWNER_HAVOC_SERIAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            PureExpr::Var(
                format!("$havoc_capture_owner_{}_{serial}", owner_local.as_u32()),
                None,
            )
        };
        let advanced = match arity {
            Some(arity) if arity > 0 && fields.keys().all(|idx| *idx < arity) => {
                let args = (0..arity)
                    .map(|idx| {
                        fields
                            .get(&idx)
                            .cloned()
                            .unwrap_or_else(|| project_capture_field(&base, idx))
                    })
                    .collect();
                PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(arity),
                    args,
                }
            }
            _ => havoc(),
        };
        if let Some(updates) = name_updates.as_mut() {
            // The substitution lane asserts each binding as a fact over the
            // source symbol, so a value still mentioning that symbol would be
            // its own premise. Refuse there rather than state it.
            let self_referential = fields.len() != arity.unwrap_or(0);
            updates.insert(
                owner_name.clone(),
                if self_referential {
                    havoc()
                } else {
                    advanced.clone()
                },
            );
        }
        local_exprs.insert(owner_local, advanced);
    }
}

#[cfg(test)]
mod thunk_shape_tests;
