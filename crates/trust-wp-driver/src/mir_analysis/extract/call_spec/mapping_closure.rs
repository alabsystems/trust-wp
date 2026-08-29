// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::{CallSiteContext, *};

/// Maximum effective basic blocks for closure body extraction.
/// Same threshold as `closure_enrichment::body_extraction`.
const TRUST_WP_MAPPING_CLOSURE_BB_THRESHOLD: usize = 6;

/// Handle `Mapping::from_closure(closure)` by extracting the closure's MIR body
/// and recording it in `CallEffects` for downstream axiom emission.
///
/// The extraction result is an opaque result variable. The closure body is
/// extracted separately (with empty user/trait specs to avoid re-entrant
/// extraction hang) and stored in effects for the encoder to consume.
///
/// Phase 3 (TODO #2316): The encoder should emit a quantified axiom:
///   `forall k. mapping.get(k) == body[param := k]`
/// Attempts to emit this directly as a `LetAssume(Forall(...))` in the
/// extraction output caused sort mismatches in the Mapping UF encoding.
/// The axiom must be emitted at the encoder layer where sort info is available.
pub(super) fn handle_mapping_from_closure<'tcx>(
    call_site: CallSiteContext<'_, 'tcx>,
    _session: &mut ExtractionSession<'_>,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    let CallSiteContext {
        tcx,
        body,
        args,
        destination,
        next_bb,
        mut local_exprs,
        visited,
        ctx,
        projected_write_facts,
    } = call_site;
    let dest_ty = body.local_decls[destination.local].ty;
    let result_var = PureExpr::Var(
        format!("call_{}", destination.local.as_u32()),
        ty_to_expr_sort_enriched(tcx, dest_ty),
    );

    if let Some((body_expr, param_names)) =
        try_extract_mapping_closure_body(tcx, body, args, ctx, &local_exprs)
    {
        effects.record_mapping_closure(result_var.clone(), body_expr, param_names);
    }

    local_exprs.insert(destination.local, result_var);
    wrap_projected_facts(
        projected_write_facts.to_vec(),
        super::extract_from_block_with_context(
            tcx,
            body,
            next_bb,
            local_exprs,
            visited,
            ctx,
            effects,
        ),
    )
}

/// Extract the closure body from a `Mapping::from_closure(closure)` call.
///
/// Returns `Some((body_expr, param_names))` if extraction succeeds.
///
/// Passes the enclosing scope's user/trait specs so trait calls like
/// `DeepModel::deep_model` are resolved rather than becoming opaque.
/// Also resolves captured variable references by substituting the
/// `__captures` placeholder with the actual captures tuple from the
/// enclosing scope's `local_exprs`, triggering tuple beta-reduction
/// so `tuple_get_N(tupleK(a, b, ...))` simplifies to the Nth capture. (#2245)
fn try_extract_mapping_closure_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    ctx: &BlockExtractionContext<'_>,
    enclosing_local_exprs: &HashMap<Local, PureExpr>,
) -> Option<(PureExpr, Vec<String>)> {
    let closure_local = match args.first()?.node {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => place.local,
        _ => return None,
    };

    let ty = body.local_decls[closure_local].ty;
    let rustc_middle::ty::TyKind::Closure(closure_def_id, _) = ty.kind() else {
        return None;
    };
    if !matches!(
        tcx.def_kind(*closure_def_id),
        rustc_hir::def::DefKind::Closure
    ) {
        return None;
    }

    if !tcx.is_mir_available(*closure_def_id) {
        return None;
    }
    let Ok(closure_body) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tcx.optimized_mir(*closure_def_id)
    })) else {
        return None;
    };

    if effective_basic_block_count(closure_body) > TRUST_WP_MAPPING_CLOSURE_BB_THRESHOLD {
        return None;
    }

    let user_param_names = resolve_arg_names_or_warn(tcx, *closure_def_id, None);
    if user_param_names.is_empty() {
        return None;
    }
    let mut param_names = Vec::with_capacity(user_param_names.len() + 1);
    param_names.push("__captures".to_string());
    param_names.extend(user_param_names.iter().cloned());

    let outcome = super::extract_return_expr_with_context_detailed(
        tcx,
        closure_body,
        &param_names,
        ctx.user_specs,
        ctx.trait_specs,
        ctx.extern_specs,
    );
    let mut body_expr = outcome.value?;

    let captures_expr = enclosing_local_exprs.get(&closure_local).cloned();
    let mut assumptions = outcome.effects.assumptions.clone();
    if let Some(ref captures) = captures_expr {
        let mut cap_subs = HashMap::new();
        cap_subs.insert("__captures".to_string(), captures.clone());
        body_expr = body_expr.substitute(&cap_subs);
        for assumption in &mut assumptions {
            *assumption = assumption.substitute(&cap_subs);
        }
    }

    let subs = collect_equality_substitutions(&assumptions);
    if !subs.is_empty() {
        body_expr = body_expr.substitute(&subs);
    }

    Some((body_expr, user_param_names))
}

/// Handle `IteratorSpec::map_inv(iter, closure)` by recording the closure's
/// per-element `#[ensures]` against the produced `MapInv` value, plus the
/// length-preservation relation to the inner iterator. (#2170 "Slice 3")
///
/// `args[0]` is the inner iterator (the receiver), `args[1]` is the mapping
/// closure. The recorded `MapInvClosureInfo` is later lowered to sound view
/// axioms by `to_view_axioms()` and folded into the function's assumption set.
///
/// The result place is treated opaquely (a fresh `call_N` var) exactly as the
/// previous Opaque fallback did, so existing behaviour for the `MapInv` value
/// itself (e.g. `completed()` delegation via the iterator rewrite) is preserved.
pub(super) fn handle_map_inv_from_closure<'tcx>(
    call_site: CallSiteContext<'_, 'tcx>,
    _session: &mut ExtractionSession<'_>,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    let CallSiteContext {
        tcx,
        body,
        args,
        destination,
        next_bb,
        mut local_exprs,
        visited,
        ctx,
        projected_write_facts,
    } = call_site;

    let dest_ty = body.local_decls[destination.local].ty;
    let result_var = PureExpr::Var(
        format!("call_{}", destination.local.as_u32()),
        ty_to_expr_sort_enriched(tcx, dest_ty),
    );

    record_map_inv_closure_ensures(tcx, body, args, ctx, &local_exprs, &result_var, effects);

    local_exprs.insert(destination.local, result_var);
    wrap_projected_facts(
        projected_write_facts.to_vec(),
        super::extract_from_block_with_context(
            tcx,
            body,
            next_bb,
            local_exprs,
            visited,
            ctx,
            effects,
        ),
    )
}

/// Recover the mapping closure from a `map_inv(iter, closure)` call and record
/// its per-element ensures + produced-length relation into `effects`.
///
/// Soundness-relevant choices:
/// - The produced length fact is emitted ONLY when the inner iterator's
///   produced length can be determined soundly. We do this for a `Range`
///   receiver (`end - start`, guarded by `start <= end` since a reversed range
///   produces zero elements). For all other receivers we emit no length fact —
///   completeness loss, never a false fact.
/// - The closure's `#[ensures]` are taken from `user_specs` (the same parsed
///   clauses the closure-enrichment pass uses), and its formal parameter names
///   from the closure's MIR. The per-element gating in `to_view_axioms` uses
///   these names to reject any clause that would leave a dangling formal.
fn record_map_inv_closure_ensures<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    ctx: &BlockExtractionContext<'_>,
    enclosing_local_exprs: &HashMap<Local, PureExpr>,
    result_var: &PureExpr,
    effects: &mut CallEffects,
) {
    // args[0] = inner iterator, args[1] = mapping closure.
    if args.len() != 2 {
        return;
    }

    // Recover the closure DefId from the closure operand's local type.
    let closure_local = match args[1].node {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => place.local,
        _ => return,
    };
    let rustc_middle::ty::TyKind::Closure(closure_def_id, _) =
        body.local_decls[closure_local].ty.kind()
    else {
        return;
    };
    if !matches!(
        tcx.def_kind(*closure_def_id),
        rustc_hir::def::DefKind::Closure
    ) {
        return;
    }

    // The closure's `#[ensures]` clauses (parsed). No ensures ⇒ only the length
    // fact is emitted (empty ensures vec).
    let ensures_exprs: Vec<PureExpr> = ctx
        .user_specs
        .get(closure_def_id)
        .map(|spec| {
            spec.ensures
                .iter()
                .filter_map(|e| trust_wp_core::contract_parser::parse_contract(e).ok())
                .collect()
        })
        .unwrap_or_default();

    // The closure's formal parameter names (element + snapshot binders). Used
    // purely as the soundness gate in `to_view_axioms`.
    let closure_param_names = resolve_arg_names_or_warn(tcx, *closure_def_id, None);

    // Compute the produced length (and its guard) for a Range receiver.
    let (produced_len, produced_len_guard) =
        range_produced_len(tcx, body, &args[0], enclosing_local_exprs)
            .map_or((None, None), |(len, guard)| (Some(len), Some(guard)));

    effects.record_map_inv_closure(
        result_var.clone(),
        produced_len,
        produced_len_guard,
        ensures_exprs,
        closure_param_names,
    );
}

/// If `arg` is a `Range` receiver, return `(produced_len, guard)` where
/// `produced_len = end@ - start@` and `guard = start@ <= end@`.
///
/// Soundness: a `Range<T>` iterator produces exactly `end - start` elements
/// when `start <= end`, and zero when `start > end`. Emitting the equality only
/// under the `start <= end` guard is therefore always true; the consumer asserts
/// `guard ==> result@.len() == produced_len`. Returns `None` for non-Range
/// receivers or when the bounds cannot be translated.
fn range_produced_len<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg: &Spanned<Operand<'tcx>>,
    enclosing_local_exprs: &HashMap<Local, PureExpr>,
) -> Option<(PureExpr, PureExpr)> {
    // The receiver type must be `core::ops::Range<_>` (start..end). Inclusive,
    // From, To, Full ranges have different element counts / no upper bound and
    // are intentionally excluded.
    let recv_ty = operand_ty(body, &arg.node)?;
    let rustc_middle::ty::TyKind::Adt(adt_def, _) = recv_ty.kind() else {
        return None;
    };
    let path = tcx.def_path_str(adt_def.did());
    if path != "core::ops::range::Range" && path != "core::ops::Range" && path != "std::ops::Range"
    {
        return None;
    }

    // The translated receiver is a 2-tuple `(start, end)`. trust-wp models a
    // `Range<T>` value as `tuple2(start, end)` where the fields are the runtime
    // bound values; the produced-element count is over their `@` (deep_model)
    // views, matching the `len()`/`size@` space used by the consuming spec.
    // Wrap each bound in `@` so the length arithmetic lives in view space.
    let iter_expr = translate_operand(&arg.node, enclosing_local_exprs)?;
    let start = PureExpr::View(Arc::new(tuple_field(&iter_expr, 0)));
    let end = PureExpr::View(Arc::new(tuple_field(&iter_expr, 1)));

    let produced_len = PureExpr::BinOp(
        Arc::new(end.clone()),
        trust_wp_core::formula::BinOp::Sub,
        Arc::new(start.clone()),
    );
    let guard = PureExpr::BinOp(
        Arc::new(start),
        trust_wp_core::formula::BinOp::Le,
        Arc::new(end),
    );
    Some((produced_len, guard))
}

/// Project the `index`-th field of a tuple expression.
///
/// When `expr` is itself a tuple constructor `__trust_wp_tuple{N}(a0, .., a{N-1})`
/// (the shape `translate_operand` produces for a `Range` value), beta-reduce
/// directly to `a{index}` so the produced length is `end - start` over the raw
/// bound expressions. The opaque `__trust_wp_tuple_get_{index}` projector UF has
/// no reduction axiom in the function-VC encoding context, so emitting it would
/// leave `tuple_get_i(tuple(a, b))` unsimplifiable and the length fact
/// undischarged. Falling back to the projector for non-constructor inputs keeps
/// the original behaviour. (#2170)
fn tuple_field(expr: &PureExpr, index: usize) -> PureExpr {
    use trust_wp_core::formula::internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_arity,
    };
    if let PureExpr::LogicFnCall { name, args } = expr {
        if let Some(arity) = tuple_logic_fn_arity(name) {
            if arity == args.len() && index < args.len() {
                return args[index].clone();
            }
        }
    }
    PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(index),
        args: vec![expr.clone()],
    }
}

/// Type of a MIR operand (the local's declared type for Copy/Move; the
/// constant's type for Constant).
fn operand_ty<'tcx>(
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<rustc_middle::ty::Ty<'tcx>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(body.local_decls[place.local].ty)
        }
        _ => None,
    }
}

/// Count effective basic blocks in a MIR body, excluding cleanup and
/// unreachable-only blocks. Mirrors `closure_enrichment::body_extraction`.
fn effective_basic_block_count(body: &Body<'_>) -> usize {
    use rustc_middle::mir::TerminatorKind;

    body.basic_blocks
        .iter()
        .filter(|bb| {
            if bb.is_cleanup {
                return false;
            }
            if bb.statements.is_empty() {
                if let Some(ref term) = bb.terminator {
                    return !matches!(
                        term.kind,
                        TerminatorKind::Unreachable
                            | TerminatorKind::UnwindResume
                            | TerminatorKind::UnwindTerminate(_)
                    );
                }
            }
            true
        })
        .count()
}

/// Collect `Var(name) == expr` equalities from call assumptions into a
/// substitution map. Used to inline opaque call result variables back into
/// the closure body expression.
///
/// Matches both `call_N` (postcondition-generated) and `_call_N`
/// (MIR-local-generated) variable names.
pub(in crate::mir_analysis::extract) fn collect_equality_substitutions(
    assumptions: &[PureExpr],
) -> HashMap<String, PureExpr> {
    let mut subs = HashMap::new();
    for assumption in assumptions {
        if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = assumption {
            match (lhs.as_ref(), rhs.as_ref()) {
                (PureExpr::Var(name, _), expr) if is_call_result_var(name) => {
                    subs.insert(name.clone(), expr.clone());
                }
                (expr, PureExpr::Var(name, _)) if is_call_result_var(name) => {
                    subs.insert(name.clone(), expr.clone());
                }
                (PureExpr::Deref(inner), expr) => {
                    if let PureExpr::Var(name, _) = inner.as_ref() {
                        if is_call_result_var(name) {
                            subs.insert(name.clone(), expr.clone());
                        }
                    }
                }
                (expr, PureExpr::Deref(inner)) => {
                    if let PureExpr::Var(name, _) = inner.as_ref() {
                        if is_call_result_var(name) {
                            subs.insert(name.clone(), expr.clone());
                        }
                    }
                }
                _ => {}
            }
        }
    }
    subs
}

/// Check if a variable name is a call result variable (e.g., `call_0`, `_call_4`).
pub(in crate::mir_analysis::extract) fn is_call_result_var(name: &str) -> bool {
    name.starts_with("call_") || name.starts_with("_call_")
}
