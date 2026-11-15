// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    fallback::handle_opaque_call,
    mapping_closure::{handle_map_inv_from_closure, handle_mapping_from_closure},
    spec_resolution::{handle_direct_spec_call, handle_extern_spec_call},
    CallSiteContext, *,
};

/// Handle a `TerminatorKind::Call` during block extraction.
///
/// This function encapsulates the entire call-site resolution chain:
/// 1. Array `.len()` folding by receiver type
/// 2. Direct user/trait spec lookup and application
/// 3. UFCS/extern spec path-based lookup chain
/// 4. Closure-aware spec resolution with capture substitution
/// 5. Try-operator (`?`) pattern recognition
/// 6. `Box::new` alias-preserving fallback
/// 7. Opaque call fallback
#[allow(clippy::too_many_arguments)]
pub(in crate::mir_analysis::extract) fn handle_call_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: rustc_middle::mir::Place<'tcx>,
    next_bb: BasicBlock,
    mut local_exprs: HashMap<Local, PureExpr>,
    visited: HashSet<BasicBlock>,
    ctx: &BlockExtractionContext<'_>,
    session: &mut ExtractionSession<'_>,
    projected_write_facts: &[(PureExpr, PureExpr)],
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    let resolved = resolve_call(
        tcx,
        body,
        bb,
        func,
        args,
        destination.local,
        ctx.user_specs,
        ctx.trait_specs,
        session.extern_specs,
        ctx.diagnostics,
        &local_exprs,
    );
    let cell_builtin = resolved
        .def_id
        .filter(|def_id| crate::provenance::is_spec_library_item(tcx, *def_id))
        .and_then(|def_id| classify_cell_builtin_path(&tcx.def_path_str(def_id)));

    if let Some(builtin) = cell_builtin {
        let call_site = CallSiteContext {
            tcx,
            body,
            args,
            destination,
            next_bb,
            local_exprs,
            visited,
            ctx,
            projected_write_facts,
        };
        return handle_cell_builtin_call(call_site, session, effects, builtin);
    }

    // Total-`Mapping` `.set(k, v)` threading (mapping_indexing; new-frontier A).
    //
    // A `snapshot!(m.set(k, v))` — or a direct `m.set(k, v)` on a `Snapshot`-
    // wrapped or bare `Mapping` — lowers `.set` as a MIR call whose result would
    // otherwise resolve to an opaque fresh `Mapping` constant via
    // `handle_opaque_call`, dropping the McCarthy read-over-write semantics. The
    // `set → mapping_set` encoder dispatch (`collection_methods.rs`) then never
    // sees a `set` `MethodCall`, so no `mapping_set` term is minted and the get-
    // over-set ground instances never fire. Bind the result local to a `set`
    // `MethodCall` over the receiver's CURRENT program-point value so downstream
    // reads (proof_assert, further `.set` chaining) mint `mapping_set(m, k, v)`.
    //
    // Sound: `mapping_set` IS the semantics of `Mapping::set`, so threading it
    // can only make entailed facts provable, never fabricate one. NARROW: only
    // `Mapping`-typed `::set` callees, and only when receiver + key + value all
    // resolve to tracked program-point expressions — otherwise fall through to
    // the normal (opaque) handling, never fabricating a receiver. (#newfrontier)
    if resolved
        .def_id
        .filter(|def_id| crate::provenance::is_spec_library_item(tcx, *def_id))
        .map(|def_id| tcx.def_path_str(def_id))
        .is_some_and(|path| is_total_mapping_set_path(&path))
        && args.len() == 3
    {
        if let (Some(receiver), Some(key), Some(value)) = (
            translate_operand(&args[0].node, &local_exprs),
            translate_operand(&args[1].node, &local_exprs),
            translate_operand(&args[2].node, &local_exprs),
        ) {
            let set_expr = PureExpr::MethodCall {
                receiver: std::sync::Arc::new(receiver),
                method: "set".to_string(),
                args: vec![key, value],
            };
            // Bind BOTH representations of this call's result to the `set` term:
            //  - `local_exprs[dest]`: the value threaded through the program-point
            //    pipeline (so a following `Snapshot::capture`/`.set` chains the
            //    nested `mapping_set`), and
            //  - an explicit `call_{dest} == set` assumption on the fresh result
            //    var: the proof_assert snapshot machinery independently names the
            //    captured set-result local `call_{dest}` and reads it in the goal,
            //    so without this the goal's `call_{dest}` stays an unconstrained
            //    free Mapping constant even though the capture-side value carries
            //    the semantics. (#newfrontier)
            let result_var = PureExpr::Var(
                format!("$call_{}", destination.local.as_u32()),
                ty_to_expr_sort_enriched(tcx, body.local_decls[destination.local].ty),
            );
            effects.assumptions.push(PureExpr::BinOp(
                std::sync::Arc::new(result_var),
                BinOp::Eq,
                std::sync::Arc::new(set_expr.clone()),
            ));
            local_exprs.insert(destination.local, set_expr);
            return wrap_projected_facts(
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
            );
        }
    }

    // NOTE (bug/869): the type-directed `snapshot!` dispatch's
    // `snapshot_capture_select(&(expr))` IS the semantic capture and now carries
    // the `SNAPSHOT_CAPTURE` spec (`result == value`), so it flows through the
    // normal spec-resolution path below exactly like a direct
    // `Snapshot::capture(&expr)` — binding its result to the captured value and
    // firing `recover_snapshot_capture_current_pointee`. Its argument-less
    // `.capture()` tail carries the identity spec (`result == self`). No opaque
    // see-through is needed: both have real specs, so `handle_opaque_call`'s
    // fail-closed `requires(false)` is never injected into the enclosing VC.
    match resolved.kind {
        ResolvedCallKind::ArrayLen(len_expr) => {
            local_exprs.insert(destination.local, len_expr);
            wrap_call_context(
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
                ),
                ctx.scope_call_context,
                &mut *session.effects,
            )
        }
        ResolvedCallKind::DirectSpec(spec) => {
            let call_site = CallSiteContext {
                tcx,
                body,
                args,
                destination,
                next_bb,
                local_exprs,
                visited,
                ctx,
                projected_write_facts,
            };
            handle_direct_spec_call(
                call_site,
                func,
                session,
                resolved.def_id.expect("DirectSpec always has def_id"),
                &spec,
                effects,
            )
        }
        ResolvedCallKind::ExternSpec(spec) => {
            let call_site = CallSiteContext {
                tcx,
                body,
                args,
                destination,
                next_bb,
                local_exprs,
                visited,
                ctx,
                projected_write_facts,
            };
            handle_extern_spec_call(
                call_site,
                func,
                session,
                resolved.def_id.expect("ExternSpec always has def_id"),
                &spec,
                effects,
            )
        }
        ResolvedCallKind::TryBranch => {
            if let Some(arg_expr) = args
                .first()
                .and_then(|a| translate_operand(&a.node, &local_exprs))
            {
                if let Some(is_option) = try_branch_type_is_option(tcx, func) {
                    if let Some(result) = try_extract_try_operator(
                        tcx,
                        body,
                        TryOperatorInput {
                            is_option,
                            arg_expr,
                            next_bb,
                            destination_local: destination.local,
                            local_exprs: local_exprs.clone(),
                            visited: visited.clone(),
                        },
                        ctx,
                        effects,
                    ) {
                        return wrap_projected_facts(projected_write_facts.to_vec(), Some(result));
                    }
                }
            }
            let call_site = CallSiteContext {
                tcx,
                body,
                args,
                destination,
                next_bb,
                local_exprs,
                visited,
                ctx,
                projected_write_facts,
            };
            handle_opaque_call(call_site, effects)
        }
        ResolvedCallKind::BoxNew => {
            if let Some(arg_expr) = translate_operand(&args[0].node, &local_exprs) {
                local_exprs.insert(destination.local, arg_expr);
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
            } else {
                let call_site = CallSiteContext {
                    tcx,
                    body,
                    args,
                    destination,
                    next_bb,
                    local_exprs,
                    visited,
                    ctx,
                    projected_write_facts,
                };
                handle_opaque_call(call_site, effects)
            }
        }
        ResolvedCallKind::IntPassthrough(int_expr)
        | ResolvedCallKind::LayoutIntrinsic(int_expr) => {
            local_exprs.insert(destination.local, int_expr);
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
        ResolvedCallKind::MappingFromClosure => {
            let call_site = CallSiteContext {
                tcx,
                body,
                args,
                destination,
                next_bb,
                local_exprs,
                visited,
                ctx,
                projected_write_facts,
            };
            handle_mapping_from_closure(call_site, session, effects)
        }
        ResolvedCallKind::MapInvFromClosure => {
            let call_site = CallSiteContext {
                tcx,
                body,
                args,
                destination,
                next_bb,
                local_exprs,
                visited,
                ctx,
                projected_write_facts,
            };
            handle_map_inv_from_closure(call_site, session, effects)
        }
        ResolvedCallKind::Opaque => {
            if std::env::var_os("TRUST_WP_AUTHORITY_TRACE").is_some() {
                eprintln!("[TWP_AUTH] opaque call: no spec resolves `{func:?}`");
            }
            let call_site = CallSiteContext {
                tcx,
                body,
                args,
                destination,
                next_bb,
                local_exprs,
                visited,
                ctx,
                projected_write_facts,
            };
            handle_opaque_call(call_site, effects)
        }
    }
}

/// Whether `path` names a total-`Mapping` `.set(key, value)` associated method:
/// either the bare `Mapping::<A, B>::set` or the deref-forwarded
/// `Snapshot::<Mapping<A, B>>::set` form. Matched by substring so it is robust to
/// the exact generic-argument spelling rustc emits in the def path. Excludes any
/// other `::set` (`Cell::set`, `PredCell::set`, permission-cell set, …) since
/// those carry no `Mapping` segment. (#newfrontier)
fn is_total_mapping_set_path(path: &str) -> bool {
    path.ends_with("::set") && path.contains("Mapping")
}
