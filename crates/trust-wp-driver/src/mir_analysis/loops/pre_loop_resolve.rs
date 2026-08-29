// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pre-loop call resolution via spec lookup.
//!
//! Resolves unresolved pre-loop function calls to `PureExpr` using `TyCtxt`
//! and extern/std spec lookup. Handles multi-call chaining (e.g.,
//! `Seq::new().into_inner()`) via multi-pass resolution.

use std::{collections::HashMap, sync::Arc};

use rustc_hir::def_id::DefId;
use rustc_middle::{mir::Local, ty::TyCtxt};
use trust_wp_core::formula::{NamedBindingValue, PureExpr};
use trust_wp_driver::{lookup_spec_with_extern, StdSpec};

use super::{
    super::{
        call_resolve::{arg_names_for_def_id, resolve_trait_method_def_id},
        effects::CallEffects,
        spec_apply::{
            apply_postconditions_for_loop_body_with_effects, apply_postconditions_with_effects,
            TranslatedArg,
        },
        translate::ty_to_expr_sort_enriched,
    },
    pre_loop_extract::UnresolvedPreLoopCall,
    CallSpecContext,
};

/// Resolve pre-loop function calls to `PureExpr` using `TyCtxt`. (#1295, #1581)
///
/// For known methods like `.len()`, produces `MethodCall { receiver: View(arg), method: "len" }`.
/// For calls with extern/std specs (e.g., `Seq::new()`), resolves via `result == <expr>`
/// postconditions. Chains through multi-call sequences by tracking resolved locals.
///
/// Returns a map of variable name → binding value for each resolved call.
pub(crate) fn resolve_pre_loop_call_locals(
    tcx: TyCtxt<'_>,
    calls: &[UnresolvedPreLoopCall],
    extern_specs: &HashMap<String, StdSpec>,
    ref_source_locals: &HashMap<Local, Local>,
) -> HashMap<Local, PureExpr> {
    resolve_pre_loop_call_locals_inner(tcx, calls, None, None, extern_specs, ref_source_locals)
}

pub(crate) fn resolve_pre_loop_call_locals_with_spec_ctx(
    spec_ctx: &CallSpecContext<'_, '_>,
    calls: &[UnresolvedPreLoopCall],
    ref_source_locals: &HashMap<Local, Local>,
) -> HashMap<Local, PureExpr> {
    resolve_pre_loop_call_locals_inner(
        spec_ctx.tcx,
        calls,
        Some(spec_ctx.user_specs),
        Some(spec_ctx.trait_specs),
        spec_ctx.extern_specs,
        ref_source_locals,
    )
}

pub(crate) fn resolve_pre_loop_calls(
    tcx: TyCtxt<'_>,
    calls: &[UnresolvedPreLoopCall],
    extern_specs: &HashMap<String, StdSpec>,
    ref_source_locals: &HashMap<Local, Local>,
) -> HashMap<String, NamedBindingValue> {
    let resolved_locals = resolve_pre_loop_call_locals(tcx, calls, extern_specs, ref_source_locals);
    let mut result = HashMap::new();
    for call in calls {
        if let (Some(name), Some(expr)) = (&call.dest_name, resolved_locals.get(&call.dest_local)) {
            result.insert(
                name.clone(),
                NamedBindingValue::new(call.dest_sort.clone(), expr.clone()),
            );
        }
        if let (Some(name), Some(local)) = (&call.receiver_name, call.receiver_local) {
            if let Some(expr) = resolved_locals.get(&local) {
                result.insert(
                    name.clone(),
                    NamedBindingValue::new(call.receiver_sort.clone(), expr.clone()),
                );
            }
        }
        // Borrow-receiver chain (#994 Phase 3 B3): when the call's receiver is a
        // reborrow temp (e.g., `_16 = &mut s`), the resolver propagates the
        // mutated value onto the source local in `resolved_locals`. Surface it
        // under the source's expr-name when the expr is a bare `Var(name, _)`.
        // This is essential for `*_ghost` mutating methods (FMap::insert_ghost,
        // FMap::remove_ghost) where the named binding for `s` must reflect the
        // post-mutation FMap so the downstream FMap-iter bridge synthesizer
        // can detect inserted (key, value) pairs.
        if let Some(receiver_local) = call.receiver_local {
            if let Some(source_local) = ref_source_locals.get(&receiver_local) {
                if let Some(expr) = resolved_locals.get(source_local) {
                    // Use the original receiver_expr (when it's a bare Var) to
                    // name the resulting binding — this is the name the user
                    // sees (e.g., "s"). Take the source's sort from that Var
                    // (the owned type, e.g., Datatype(N)) rather than the
                    // reborrow's MutRef sort.
                    if let Some(PureExpr::Var(name, source_sort)) = &call.receiver_expr {
                        result.insert(
                            name.clone(),
                            NamedBindingValue::new(source_sort.clone(), expr.clone()),
                        );
                    }
                }
            }
        }
    }
    result
}

pub(crate) fn resolve_pre_loop_call_facts_with_spec_ctx(
    spec_ctx: &CallSpecContext<'_, '_>,
    calls: &[UnresolvedPreLoopCall],
    ref_source_locals: &HashMap<Local, Local>,
) -> Vec<PureExpr> {
    let resolved_locals = resolve_pre_loop_call_locals_inner(
        spec_ctx.tcx,
        calls,
        Some(spec_ctx.user_specs),
        Some(spec_ctx.trait_specs),
        spec_ctx.extern_specs,
        ref_source_locals,
    );

    let mut facts = Vec::new();
    for call in calls {
        let Some(name) = &call.dest_name else {
            continue;
        };
        let path = spec_ctx.tcx.def_path_str(call.def_id);
        let trait_path = resolve_trait_method_def_id(spec_ctx.tcx, call.def_id)
            .map(|tid| spec_ctx.tcx.def_path_str(tid));
        append_call_postcondition_facts(
            spec_ctx.tcx,
            call,
            name,
            &path,
            trait_path.as_deref(),
            Some(spec_ctx.user_specs),
            Some(spec_ctx.trait_specs),
            spec_ctx.extern_specs,
            &resolved_locals,
            &mut facts,
        );
    }

    facts
}

pub(crate) fn resolve_pre_loop_call_facts_for_local_names_with_spec_ctx(
    spec_ctx: &CallSpecContext<'_, '_>,
    calls: &[UnresolvedPreLoopCall],
    ref_source_locals: &HashMap<Local, Local>,
    local_names: &HashMap<Local, String>,
) -> Vec<PureExpr> {
    if local_names.is_empty() {
        return Vec::new();
    }

    let resolved_locals = resolve_pre_loop_call_locals_inner(
        spec_ctx.tcx,
        calls,
        Some(spec_ctx.user_specs),
        Some(spec_ctx.trait_specs),
        spec_ctx.extern_specs,
        ref_source_locals,
    );

    let mut facts = Vec::new();
    for call in calls {
        let Some(name) = local_names.get(&call.dest_local) else {
            continue;
        };
        let path = spec_ctx.tcx.def_path_str(call.def_id);
        let trait_path = resolve_trait_method_def_id(spec_ctx.tcx, call.def_id)
            .map(|tid| spec_ctx.tcx.def_path_str(tid));
        append_call_postcondition_facts(
            spec_ctx.tcx,
            call,
            name,
            &path,
            trait_path.as_deref(),
            Some(spec_ctx.user_specs),
            Some(spec_ctx.trait_specs),
            spec_ctx.extern_specs,
            &resolved_locals,
            &mut facts,
        );
    }

    facts
}

fn resolve_pre_loop_call_locals_inner(
    tcx: TyCtxt<'_>,
    calls: &[UnresolvedPreLoopCall],
    user_specs: Option<&HashMap<DefId, StdSpec>>,
    trait_specs: Option<&HashMap<DefId, StdSpec>>,
    extern_specs: &HashMap<String, StdSpec>,
    ref_source_locals: &HashMap<Local, Local>,
) -> HashMap<Local, PureExpr> {
    // Track resolved expressions by MIR Local for multi-call chaining (#1581).
    let mut resolved_locals: HashMap<Local, PureExpr> = HashMap::new();

    // Multi-pass resolution: up to N passes to handle call chains.
    // Each pass resolves calls whose arguments are now available from
    // previous passes. Typically 2 passes suffice (e.g., Seq::new() → into_inner()).
    let max_passes = 3;
    let mut remaining: Vec<usize> = (0..calls.len()).collect();
    // Track which call indices have already applied their mutating-receiver
    // update so multi-pass iteration does not double-apply chained writes
    // (e.g., insert_ghost in a stuck `still_remaining` slot would otherwise
    // be re-resolved on every pass, producing `s.insert(k,v).insert(k,v)`).
    // (#994 Phase 3 B3)
    let mut mutating_receiver_done: std::collections::HashSet<usize> =
        std::collections::HashSet::new();

    let dump = std::env::var_os("TRUST_WP_PRE_LOOP_RESOLVE_DUMP").is_some();

    for _pass in 0..max_passes {
        if remaining.is_empty() {
            break;
        }
        let mut still_remaining = Vec::new();
        for &idx in &remaining {
            let call = &calls[idx];
            let path = tcx.def_path_str(call.def_id);
            let trait_path =
                resolve_trait_method_def_id(tcx, call.def_id).map(|tid| tcx.def_path_str(tid));
            let method_name = extract_method_name(&path, trait_path.as_deref());
            if dump {
                eprintln!(
                    "PRE_LOOP_RESOLVE pass={} idx={} path={} method={:?} dest_name={:?} \
                     receiver_local={:?} receiver_name={:?} arg_locals={:?} arg_exprs={:?}",
                    _pass,
                    idx,
                    path,
                    method_name,
                    call.dest_name,
                    call.receiver_local,
                    call.receiver_name,
                    call.arg_locals,
                    call.arg_exprs,
                );
            }

            // Try to re-translate receiver using resolved locals from previous passes.
            // Also follow borrow chains via ref_source_locals: when MIR has
            // `_ref = &_call_result`, the receiver arg points to `_ref` but the
            // actual value lives at `_call_result`. (#2665)
            let receiver_expr = call.receiver_expr.clone().or_else(|| {
                call.arg_locals
                    .first()
                    .and_then(|opt_local| opt_local.as_ref())
                    .and_then(|local| {
                        resolved_locals.get(local).cloned().or_else(|| {
                            // Follow Ref chain: _ref → _source → resolved_locals (#2665)
                            ref_source_locals
                                .get(local)
                                .and_then(|source| resolved_locals.get(source).cloned())
                        })
                    })
            });

            // Check whether the full path is a Snapshot::capture call.
            let is_snapshot_capture = path.contains("Snapshot") && method_name == Some("capture");

            // Whether this call constructs an empty `FMap` (`FMap::new()` /
            // `FMap::empty()`). Resolving the result to the canonical
            // `fmap_empty()` constructor (rather than an opaque fresh var) lets
            // the encoder's FMap emptiness axioms apply — `len(empty) == 0`,
            // `forall k. !contains(empty, k)` — so a subsequent single insert
            // yields a provable singleton `len == 1`. SOUND: `FMap::new()` is
            // definitionally the empty map (its `EMPTY` spec ensures
            // `result.len() == 0 && forall k. !contains(result, k)`), and the
            // spec carries no `result == <expr>` clause, so pattern resolution
            // here is the only place this emptiness reaches the VC. (cc/fmap)
            let is_fmap_empty_ctor = matches!(method_name, Some("new") | Some("empty"))
                && call.arg_locals.iter().all(Option::is_none)
                && path.contains("FMap::")
                && !path.contains("FMapGhostSplit");

            // Pass 1: pattern-based resolution (original logic).
            let mut resolved = match method_name {
                _ if is_fmap_empty_ctor => Some(PureExpr::LogicFnCall {
                    name: "fmap_empty".to_string(),
                    args: vec![],
                }),
                Some("len") => receiver_expr.as_ref().map(|recv| PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(recv.clone()))),
                    method: "len".to_string(),
                    args: vec![],
                }),
                Some("capture") if is_snapshot_capture => receiver_expr.clone(),
                // `view(x)` free function → PureExpr::View(x). (#2665)
                // Handles `snapshot!(x@)` which expands to `view(x)` then `capture(&view_result)`.
                Some("view") => receiver_expr
                    .as_ref()
                    .map(|recv| PureExpr::View(Arc::new(recv.clone()))),
                _ => None,
            };

            // Pass 2: spec-based resolution (#1581).
            // Look up extern/std specs and extract `result == <expr>` postconditions.
            if resolved.is_none() {
                resolved = resolve_call_via_spec(
                    tcx,
                    call.def_id,
                    &path,
                    trait_path.as_deref(),
                    call.dest_local,
                    call.dest_sort.clone(),
                    receiver_expr.as_ref(),
                    &call.arg_exprs,
                    &call.arg_locals,
                    &resolved_locals,
                    user_specs,
                    trait_specs,
                    extern_specs,
                );
            }

            if let Some(expr) = resolved {
                if dump {
                    eprintln!("PRE_LOOP_RESOLVE  -> dest resolved: {:?}", expr);
                }
                resolved_locals.insert(call.dest_local, expr.clone());
            } else {
                still_remaining.push(idx);
            }

            if !mutating_receiver_done.contains(&idx) {
                if let (Some(receiver_local), Some(receiver_expr)) =
                    (call.receiver_local, receiver_expr.as_ref())
                {
                    // For reborrow receivers (`_16 = &mut s`), prefer the resolved
                    // source-local expression so a chain like
                    // `s = into_inner_result; s.insert_ghost(k, v)` produces
                    // `MethodCall(receiver=into_inner_result, method=insert, args=[k, v])`
                    // rather than the self-referential
                    // `MethodCall(receiver=Var("s"), method=insert, ...)`. (#994 Phase 3 B3)
                    let effective_receiver = ref_source_locals
                        .get(&receiver_local)
                        .and_then(|source| resolved_locals.get(source).cloned())
                        .unwrap_or_else(|| receiver_expr.clone());
                    if let Some(updated_receiver) = resolve_mutating_receiver_via_method(
                        method_name,
                        &effective_receiver,
                        &call.arg_locals,
                        &call.arg_exprs,
                        &resolved_locals,
                    ) {
                        if dump {
                            eprintln!(
                                "PRE_LOOP_RESOLVE  -> mutating receiver updated: local={:?} expr={:?}",
                                receiver_local, updated_receiver
                            );
                        }
                        mutating_receiver_done.insert(idx);
                        resolved_locals.insert(receiver_local, updated_receiver.clone());
                        // Propagate to borrow source: `_16 = &mut s` then mutating
                        // call through `_16` writes to `s`. (#994 Phase 3 B3)
                        if let Some(&source_local) = ref_source_locals.get(&receiver_local) {
                            if dump {
                                eprintln!(
                                    "PRE_LOOP_RESOLVE  -> propagating to ref source local={:?}",
                                    source_local
                                );
                            }
                            resolved_locals.insert(source_local, updated_receiver);
                        }
                    }
                }
            }
        }
        if still_remaining.len() == remaining.len() {
            break; // No progress — stop iterating.
        }
        remaining = still_remaining;
    }
    resolved_locals
}

#[allow(clippy::too_many_arguments)]
fn append_call_postcondition_facts(
    tcx: TyCtxt<'_>,
    call: &UnresolvedPreLoopCall,
    dest_name: &str,
    path: &str,
    trait_path: Option<&str>,
    user_specs: Option<&HashMap<DefId, StdSpec>>,
    trait_specs: Option<&HashMap<DefId, StdSpec>>,
    extern_specs: &HashMap<String, StdSpec>,
    resolved_locals: &HashMap<Local, PureExpr>,
    facts: &mut Vec<PureExpr>,
) {
    let Some(spec) = lookup_pre_loop_spec(
        call.def_id,
        path,
        trait_path,
        user_specs,
        trait_specs,
        extern_specs,
    ) else {
        return;
    };
    if spec.ensures.is_empty() {
        return;
    }

    let sig = tcx.fn_sig(call.def_id).instantiate_identity().skip_binder();
    let receiver_expr = call_effective_receiver_expr(call, resolved_locals);
    let translated_args = translated_args_for_pre_loop_call(
        tcx,
        &sig,
        receiver_expr.as_ref(),
        &call.arg_exprs,
        &call.arg_locals,
        resolved_locals,
    );
    let hir_param_names = arg_names_for_def_id(tcx, call.def_id);
    let param_names = spec.param_names.clone().or(hir_param_names);
    let result_var = PureExpr::Var(dest_name.to_string(), call.dest_sort.clone());
    let mut effects = CallEffects::new();
    let _ = apply_postconditions_with_effects(
        &spec.ensures,
        &result_var,
        &translated_args,
        param_names.as_deref(),
        &mut effects,
        true,
    );

    for fact in effects.assumptions {
        if !facts.contains(&fact) {
            facts.push(fact);
        }
    }
}

fn call_effective_receiver_expr(
    call: &UnresolvedPreLoopCall,
    resolved_locals: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    call.arg_locals
        .first()
        .and_then(|opt_local| opt_local.as_ref())
        .and_then(|local| resolved_locals.get(local).cloned())
        .or_else(|| call.receiver_expr.clone())
        .or_else(|| call.arg_exprs.first().and_then(|expr| expr.clone()))
}

fn translated_args_for_pre_loop_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig: &rustc_middle::ty::FnSig<'tcx>,
    receiver_expr: Option<&PureExpr>,
    arg_exprs: &[Option<PureExpr>],
    arg_locals: &[Option<Local>],
    resolved_locals: &HashMap<Local, PureExpr>,
) -> Vec<TranslatedArg> {
    let arg_count = arg_locals.len().max(arg_exprs.len());
    (0..arg_count)
        .map(|idx| {
            let expr = arg_locals
                .get(idx)
                .and_then(|opt_local| {
                    opt_local
                        .as_ref()
                        .and_then(|local| resolved_locals.get(local))
                })
                .cloned()
                .or_else(|| (idx == 0).then(|| receiver_expr.cloned()).flatten())
                .or_else(|| arg_exprs.get(idx).and_then(|expr| expr.clone()));
            expr.map_or_else(
                || {
                    let sort = sig
                        .inputs()
                        .get(idx)
                        .and_then(|ty| ty_to_expr_sort_enriched(tcx, *ty));
                    TranslatedArg::fallback(PureExpr::Var(format!("arg{idx}"), sort))
                },
                TranslatedArg::new,
            )
        })
        .collect()
}

/// Resolve a single pre-loop call via extern/std spec lookup. (#1581)
///
/// Looks up the callee's spec and extracts `result == <expr>` postconditions,
/// substituting call-site arguments. Used for calls like `Seq::new()` (which
/// has `ensures: result == seq_empty()`) and `into_inner(self)` (which has
/// `ensures: result == self`).
#[allow(clippy::too_many_arguments)] // Phase C (#963): extern_specs added temporarily; consolidate in Phase D.
fn resolve_call_via_spec(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    path: &str,
    trait_path: Option<&str>,
    dest_local: Local,
    result_sort: Option<trust_wp_core::formula::ExprSort>,
    receiver_expr: Option<&PureExpr>,
    arg_exprs: &[Option<PureExpr>],
    arg_locals: &[Option<Local>],
    resolved_locals: &HashMap<Local, PureExpr>,
    user_specs: Option<&HashMap<DefId, StdSpec>>,
    trait_specs: Option<&HashMap<DefId, StdSpec>>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Option<PureExpr> {
    let spec = lookup_pre_loop_spec(
        def_id,
        path,
        trait_path,
        user_specs,
        trait_specs,
        extern_specs,
    )?;

    if spec.ensures.is_empty() {
        return None;
    }

    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();

    let translated_args = translated_args_for_pre_loop_call(
        tcx,
        &sig,
        receiver_expr,
        arg_exprs,
        arg_locals,
        resolved_locals,
    );

    let hir_param_names = arg_names_for_def_id(tcx, def_id);
    let param_names = spec.param_names.clone().or(hir_param_names);

    let result_var = PureExpr::Var(
        format!("call_{}", dest_local.as_u32()),
        result_sort.or_else(|| ty_to_expr_sort_enriched(tcx, sig.output())),
    );
    // Effects (assumptions/obligations) are collected but not consumed — pre-loop
    // call resolution only needs the return expression. (#963)
    let mut call_effects = CallEffects::new();
    let result_expr = apply_postconditions_for_loop_body_with_effects(
        &spec.ensures,
        &result_var,
        &translated_args,
        param_names.as_deref(),
        &mut call_effects,
    );

    // If the result is still the plain variable, the spec had no
    // `result == <expr>` postcondition.
    if result_expr == result_var && call_effects.assumptions.is_empty() {
        return None;
    }

    Some(result_expr)
}

fn resolve_mutating_receiver_via_method(
    method_name: Option<&str>,
    receiver_expr: &PureExpr,
    arg_locals: &[Option<Local>],
    arg_exprs: &[Option<PureExpr>],
    resolved_locals: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    let method = match method_name {
        Some("insert_ghost") => "insert",
        Some("remove_ghost") => "remove",
        _ => return None,
    };

    // Fall back to extract-time arg_exprs when resolved_locals lacks a binding.
    // Plain non-call locals like `bor_k = &mut k` are not entered into
    // resolved_locals (which only tracks call results), but their symbolic
    // Var representation is captured in arg_exprs via the extract-time
    // translation. (#994 Phase 3 B3)
    let args: Vec<PureExpr> = arg_locals
        .iter()
        .enumerate()
        .skip(1)
        .map(|(idx, local)| {
            local
                .and_then(|l| resolved_locals.get(&l).cloned())
                .or_else(|| arg_exprs.get(idx).and_then(|expr| expr.clone()))
        })
        .collect::<Option<Vec<_>>>()?;

    Some(PureExpr::MethodCall {
        receiver: Arc::new(receiver_expr.clone()),
        method: method.to_string(),
        args,
    })
}

fn lookup_pre_loop_spec(
    def_id: DefId,
    path: &str,
    trait_path: Option<&str>,
    user_specs: Option<&HashMap<DefId, StdSpec>>,
    trait_specs: Option<&HashMap<DefId, StdSpec>>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Option<StdSpec> {
    if let Some(spec) = user_specs.and_then(|specs| specs.get(&def_id)) {
        return Some(spec.clone());
    }
    if let Some(spec) = trait_specs.and_then(|specs| specs.get(&def_id)) {
        return Some(spec.clone());
    }

    // Look up spec: extern_specs → std_specs → trait method fallback.
    // Phase C (#963): uses explicit extern_specs parameter instead of EXTERN_SPECS thread-local.
    let extern_opt = if extern_specs.is_empty() {
        None
    } else {
        Some(extern_specs)
    };
    lookup_spec_with_extern(extern_opt, path).or_else(|| {
        let trait_path = trait_path?;
        lookup_spec_with_extern(extern_opt, trait_path)
    })
}

/// Extract the method name from a def path like `core::slice::<impl [u8]>::len`
/// or a trait path like `core::iter::ExactSizeIterator::len`.
fn extract_method_name<'a>(path: &'a str, trait_path: Option<&'a str>) -> Option<&'a str> {
    // Try trait path first (more canonical).
    if let Some(tp) = trait_path {
        if let Some(name) = tp.rsplit("::").next() {
            return Some(name);
        }
    }
    // Fall back to impl path: last `::` segment.
    path.rsplit("::").next()
}
