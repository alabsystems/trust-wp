// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-result resolution helpers for substitution extraction.
//!
//! These functions support the block-walking pipeline in [`super`].
//! `call_result_expr_for_substitutions` resolves function calls against user
//! specs, extern specs, and trait method fallbacks. `resolve_ref_to_named_local`
//! preserves mutable-reference variable identity.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{BasicBlock, Body, Local, Location, Operand, Place, ProjectionElem, Rvalue},
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
        closure::{
            call_result_for_interior_mutable_args, resolve_closure_arg_return_values,
            untupled_closure_call_args,
        },
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
        .filter(|def_id| crate::provenance::is_spec_library_item(ctx.tcx, *def_id))
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
                &crate::mir_analysis::call_signature(
                    ctx.tcx,
                    def_id,
                    param_names,
                    Some(crate::mir_analysis::CallSite { body, func }),
                ),
                &result_var,
                &translated_args,
                param_names,
                &mut effects,
                false,
            );
            let resolved_expr = if preserves_empty_seq_constructor_carrier(&resolved_expr) {
                result_var.clone()
            } else {
                resolved_expr
            };
            // See the ExternSpec branch / `recover_snapshot_capture_current_pointee`.
            let resolved_expr = recover_snapshot_capture_current_pointee(
                ctx.tcx,
                body,
                def_id,
                args,
                resolved_expr,
            );
            // The shared interior-mutability rule for a call result: the same
            // decision the primary lane applies in `call_spec/spec_resolution.rs`.
            // Without it this lane re-derives, from the pre-call receiver, the
            // very read result the primary lane deliberately makes fresh — so
            // two reads around one write through the same `&Cell` become one
            // term and a false `a == b` discharges.
            call_result_for_interior_mutable_args(ctx.tcx, body, args, resolved_expr, &result_var)
            // effects dropped — substitution pass; thread-locals cleared before main extraction
        }
        ResolvedCallKind::ExternSpec(spec) => {
            // Closure-aware resolution: when the extern/std_specs match is a
            // Fn/FnOnce/FnMut trait call and the concrete closure has user specs,
            // use the closure's own spec with untupled arguments.
            let def_id = resolved.def_id.expect("ExternSpec always has def_id");
            let (
                (effective_spec, effective_args, effective_param_names, effective_self_expr),
                effective_def_id,
            ) = if let Some(closure_def_id) = extract_closure_def_id_from_fn_call(func) {
                if let Some(closure_spec) = ctx.user_specs.get(&closure_def_id) {
                    let closure_args = untupled_closure_call_args(
                        ctx.tcx,
                        closure_def_id,
                        translate_call_args_for_substitutions_with_tcx(
                            &args[1.min(args.len())..],
                            local_exprs,
                            Some(body),
                            Some(ctx.tcx),
                        ),
                    );
                    let closure_param_names = arg_names_for_def_id(ctx.tcx, closure_def_id);
                    let closure_self_expr = args
                        .first()
                        .and_then(|arg| translate_operand(&arg.node, local_exprs));
                    (
                        (
                            closure_spec.clone(),
                            closure_args,
                            closure_param_names,
                            closure_self_expr,
                        ),
                        closure_def_id,
                    )
                } else {
                    (
                        resolve_extern_spec_args_for_subst(
                            ctx,
                            body,
                            func,
                            args,
                            local_exprs,
                            def_id,
                            &spec,
                        ),
                        def_id,
                    )
                }
            } else if let Some(fn_def_id) = extract_fn_item_def_id_from_fn_trait_call(func) {
                // Function item called through Fn trait dispatch.
                if let Some(fn_spec) = ctx.user_specs.get(&fn_def_id) {
                    let fn_args = translate_call_args_for_substitutions_with_tcx(
                        &args[1.min(args.len())..],
                        local_exprs,
                        Some(body),
                        Some(ctx.tcx),
                    );
                    let fn_param_names = arg_names_for_def_id(ctx.tcx, fn_def_id);
                    ((fn_spec.clone(), fn_args, fn_param_names, None), fn_def_id)
                } else {
                    (
                        resolve_extern_spec_args_for_subst(
                            ctx,
                            body,
                            func,
                            args,
                            local_exprs,
                            def_id,
                            &spec,
                        ),
                        def_id,
                    )
                }
            } else {
                (
                    resolve_extern_spec_args_for_subst(
                        ctx,
                        body,
                        func,
                        args,
                        local_exprs,
                        def_id,
                        &spec,
                    ),
                    def_id,
                )
            };
            let mut effects = CallEffects::new();
            let resolved_expr = apply_postconditions_with_self_and_effects(
                &effective_spec.ensures,
                &crate::mir_analysis::call_signature(
                    ctx.tcx,
                    effective_def_id,
                    effective_param_names.as_deref(),
                    Some(crate::mir_analysis::CallSite { body, func }),
                ),
                &result_var,
                &effective_args,
                effective_param_names.as_deref(),
                effective_self_expr.as_ref(),
                &mut effects,
            );
            let resolved_expr = if preserves_empty_seq_constructor_carrier(&resolved_expr) {
                result_var.clone()
            } else {
                resolved_expr
            };
            // `snapshot!(*a)` of a `&mut T` deref resolves through this extern
            // `Snapshot::capture` spec. Freeze the CURRENT pointee value at the
            // capture point instead of aliasing the mut-ref identity (which the
            // substitution pass later advances to its prophecy/final after the
            // intervening `add_some(a)` call). Without this, `*a_p` follows
            // `^a` and `*a > *a_p` collapses to `^a > ^a` (unprovable).
            let resolved_expr = recover_snapshot_capture_current_pointee(
                ctx.tcx,
                body,
                def_id,
                args,
                resolved_expr,
            );
            // The shared interior-mutability rule for a call result — see the
            // DirectSpec arm above.
            call_result_for_interior_mutable_args(ctx.tcx, body, args, resolved_expr, &result_var)
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
/// writes like `*swap_refs((&mut a, &mut b)).0 = 10` to resolve back to `b`.
/// Resolve a `&mut` rvalue to the named local it references, using enriched
/// ADT sort resolution via the provided `TyCtxt`.
pub(super) fn resolve_ref_to_named_local<'tcx>(
    rvalue: &Rvalue<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    local_exprs: &HashMap<Local, PureExpr>,
    tcx: TyCtxt<'tcx>,
) -> Option<PureExpr> {
    let Rvalue::Ref(_, borrow_kind, ref_place) = rvalue else {
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
            } else if shared_borrow_reads_param_binding(tcx, body, *borrow_kind, ref_place.local) {
                return Some(expr.clone());
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
        // state so sequential calls receive the updated receiver.
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

/// Whether a shared borrow of the local `local` reads the local's binding at
/// the borrow rather than naming the local (D-241): `local` is a by-value
/// parameter of a function item whose type is `Freeze`, so no write can
/// change it while the borrow lives. Named, the borrow would be read through
/// the parameter's own name, which inside a recorded value is its ENTRY value
/// once the `proof_assert` lane names that apart from its value at the
/// assertion; a store before the borrow (`x = 5; read(&x)`) would then be
/// read as the value before it.
fn shared_borrow_reads_param_binding<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_kind: rustc_middle::mir::BorrowKind,
    local: Local,
) -> bool {
    use rustc_middle::mir::BorrowKind;

    matches!(borrow_kind, BorrowKind::Shared | BorrowKind::Fake(_))
        && (1..=body.arg_count).contains(&local.as_usize())
        && !tcx.is_closure_like(body.source.def_id())
        && {
            let ty = body.local_decls[local].ty;
            !ty.is_any_ptr()
                && !ty.is_box()
                && ty.is_freeze(
                    tcx,
                    rustc_middle::ty::TypingEnv::post_analysis(tcx, body.source.def_id()),
                )
        }
}

/// Whether `place` reborrows through a dereference of a `&mut` reference —
/// Creusot's `DerefMutBor`. Box derefs and shared-reference derefs do not count.
pub(super) fn is_mut_ref_reborrow_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
) -> bool {
    place.iter_projections().any(|(base, elem)| {
        matches!(elem, ProjectionElem::Deref)
            && matches!(
                base.ty(body, tcx).ty.kind(),
                rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
            )
    })
}

/// Collect the `&mut` reborrow sites that are FINAL reborrows in Creusot's
/// sense, by running the same `NotFinalPlaces` backward dataflow Creusot uses
/// (`creusot/src/analysis/not_final_places.rs`) and querying it right after
/// each borrow statement (Creusot: `is_final_at(.., loc.successor_within_block())`).
///
/// Soundness: a final reborrow inherits the parent's id and ties its final
/// value to the parent (`borrow_final`); a non-final one gets a fresh,
/// unconstrained id and no final link (`borrow_mut`). Callers treat every
/// reborrow site NOT in this set as non-final — the fail-closed direction.
pub(super) fn final_reborrow_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> HashSet<Location> {
    use rustc_middle::mir::{BorrowKind, StatementKind};
    use rustc_mir_dataflow::Analysis;

    let mut sites = HashSet::new();
    let has_reborrow = body.basic_blocks.iter().any(|block| {
        block.statements.iter().any(|stmt| {
            matches!(&stmt.kind, StatementKind::Assign((_, Rvalue::Ref(_, BorrowKind::Mut { .. }, place)))
                if is_mut_ref_reborrow_place(tcx, body, place))
        })
    });
    if !has_reborrow {
        return sites;
    }
    // Creusot runs `NotFinalPlaces` on MIR from which `cleanup_spec_closures`
    // has removed every snapshot capture, so a `snapshot!(&mut **x)` never
    // makes an earlier `&mut **x` non-final there (should_succeed/bug/
    // final_borrows::write_inner_borrow). trust-wp's `snapshot!` lowers to a
    // real phantom borrow instead; skip exactly those borrow statements.
    let analysis = crate::mir_analysis::not_final_places::NotFinalPlaces::new_ignoring(
        tcx,
        body,
        snapshot_capture_mut_borrow_sites(tcx, body),
    );
    let results = analysis.iterate_to_fixpoint(tcx, body, None);
    let mut cursor = results.into_results_cursor(body);
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            let StatementKind::Assign((_, Rvalue::Ref(_, BorrowKind::Mut { .. }, place))) =
                &stmt.kind
            else {
                continue;
            };
            if !is_mut_ref_reborrow_place(tcx, body, place) {
                continue;
            }
            let location = Location {
                block,
                statement_index,
            };
            if crate::mir_analysis::not_final_places::NotFinalPlaces::is_final_at(
                &mut cursor,
                place,
                location,
            )
            .is_some()
            {
                sites.insert(location);
            }
        }
    }
    sites
}

/// The `&mut` borrow statements whose only consumer is a `snapshot!` capture:
/// `_t = &mut P; _r = &_t; [_r2 = &*_r;] snapshot_capture_select(_r2)` (or a
/// direct `Snapshot::capture(_r)`), following plain `move`/`copy` hops between
/// the borrow and `_t` within the call's block.
///
/// Soundness of ignoring them for finality: both capture entry points are
/// zero-sized phantoms (`trust-wp-std/src/ghost.rs`) — they neither write
/// through the captured `&mut`, nor store it, nor return it (the `&mut`-aware
/// capture's output lifetime is decoupled from the loan), so the borrow is
/// never written and cannot change the value any other borrow of `P` resolves
/// to. It is ghost code, and Creusot erases it before the same analysis. A
/// shape this matcher does not recognise is simply not ignored, which keeps
/// the conservative (non-final) classification.
pub(super) fn snapshot_capture_mut_borrow_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> HashSet<Location> {
    use rustc_middle::mir::{BorrowKind, StatementKind, TerminatorKind};

    // Candidate: (borrow location, hop-chain locals, locations where those
    // locals may legitimately appear).
    let mut candidates: Vec<(Location, Vec<Local>, HashSet<Location>)> = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let Some(terminator) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            continue;
        };
        let Operand::Constant(constant) = func else {
            continue;
        };
        let rustc_middle::ty::TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
            continue;
        };
        if !crate::provenance::is_spec_library_item(tcx, *def_id)
            || !is_trust_wp_std_snapshot_capture(tcx, *def_id)
        {
            continue;
        }
        let Some(arg) = args.last() else {
            continue;
        };
        let (Operand::Copy(arg_place) | Operand::Move(arg_place)) = &arg.node else {
            continue;
        };
        if !arg_place.projection.is_empty() {
            continue;
        }
        let call_location = Location {
            block,
            statement_index: data.statements.len(),
        };
        // Walk the block backwards from the call: `arg = &tmp`, then
        // `tmp = move/copy tmp2` hops, ending at `tmpN = &mut P`.
        let mut want = arg_place.local;
        let mut chain = vec![want];
        let mut allowed = HashSet::from([call_location]);
        let mut seen_shared_ref = false;
        for (statement_index, stmt) in data.statements.iter().enumerate().rev() {
            let StatementKind::Assign((dest, rvalue)) = &stmt.kind else {
                continue;
            };
            if dest.local != want || !dest.projection.is_empty() {
                continue;
            }
            let location = Location {
                block,
                statement_index,
            };
            allowed.insert(location);
            match rvalue {
                // `_7 = &(*_8)`: shared reborrow of the `&` temp itself.
                Rvalue::Ref(_, BorrowKind::Shared, referent)
                    if !seen_shared_ref
                        && referent.projection.len() == 1
                        && matches!(referent.projection[0], ProjectionElem::Deref)
                        && matches!(
                            body.local_decls[referent.local].ty.kind(),
                            rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not)
                        ) =>
                {
                    want = referent.local;
                    chain.push(want);
                }
                // `_8 = &_9`: the inline `&(expr)` of the capture.
                Rvalue::Ref(_, BorrowKind::Shared, referent)
                    if !seen_shared_ref && referent.projection.is_empty() =>
                {
                    seen_shared_ref = true;
                    want = referent.local;
                    chain.push(want);
                }
                Rvalue::Use(Operand::Move(src) | Operand::Copy(src), _)
                    if seen_shared_ref && src.projection.is_empty() =>
                {
                    want = src.local;
                    chain.push(want);
                }
                Rvalue::Ref(_, BorrowKind::Mut { .. }, _) if seen_shared_ref => {
                    candidates.push((location, chain, allowed));
                    break;
                }
                _ => break,
            }
        }
    }

    // Sole-consumer check: a hop-chain local that appears ANYWHERE else in the
    // body (a projected write `(*t) = 1` inside a side-effecting
    // `snapshot!({ let t = &mut *bor; *t = 1; t })`, a later `*t = 1` through a
    // user-named `t`, a further reborrow `&mut *t`, ...) means the borrow is
    // NOT only consumed by the phantom capture: keep it (non-final analysis).
    struct ChainUses<'a> {
        chain: &'a [Local],
        allowed: &'a HashSet<Location>,
        foreign_use: bool,
    }
    impl<'tcx> rustc_middle::mir::visit::Visitor<'tcx> for ChainUses<'_> {
        fn visit_local(
            &mut self,
            local: Local,
            context: rustc_middle::mir::visit::PlaceContext,
            location: Location,
        ) {
            if matches!(context, rustc_middle::mir::visit::PlaceContext::NonUse(_)) {
                return;
            }
            if self.chain.contains(&local) && !self.allowed.contains(&location) {
                self.foreign_use = true;
            }
        }
    }
    let mut sites = HashSet::new();
    for (borrow_location, chain, allowed) in candidates {
        let mut uses = ChainUses {
            chain: &chain,
            allowed: &allowed,
            foreign_use: false,
        };
        rustc_middle::mir::visit::Visitor::visit_body(&mut uses, body);
        if !uses.foreign_use {
            sites.insert(borrow_location);
        }
    }
    sites
}

/// Whether `def_id` is one of trust-wp-std's two snapshot capture entry points,
/// resolved by definition rather than by path text (a user type or module
/// named `Snapshot` must not match): the free function
/// `trust_wp_std::ghost::snapshot_capture_select`, or `capture` in an INHERENT
/// impl of `trust_wp_std::ghost::Snapshot`. Both are zero-sized phantoms.
pub(super) fn is_trust_wp_std_snapshot_capture(
    tcx: TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
) -> bool {
    use rustc_hir::def::DefKind;

    let is_std_crate =
        |id: rustc_hir::def_id::DefId| tcx.crate_name(id.krate).as_str() == "trust_wp_std";
    if !is_std_crate(def_id) {
        return false;
    }
    let Some(name) = tcx.opt_item_name(def_id) else {
        return false;
    };
    match name.as_str() {
        "snapshot_capture_select" => matches!(tcx.def_kind(def_id), DefKind::Fn),
        "capture" => {
            if !matches!(tcx.def_kind(def_id), DefKind::AssocFn) {
                return false;
            }
            let Some(parent) = tcx.opt_parent(def_id) else {
                return false;
            };
            if !matches!(tcx.def_kind(parent), DefKind::Impl { of_trait: false }) {
                return false;
            }
            let rustc_middle::ty::TyKind::Adt(adt, _) = tcx
                .type_of(parent)
                .instantiate_identity()
                .skip_norm_wip()
                .kind()
            else {
                return false;
            };
            is_std_crate(adt.did())
                && tcx
                    .opt_item_name(adt.did())
                    .is_some_and(|n| n.as_str() == "Snapshot")
        }
        _ => false,
    }
}

/// Fresh per-borrow-site carrier for a NON-final `&mut` reborrow: a distinct
/// symbol per MIR location, so the child is never identified with the parent's
/// carrier nor with another borrow of the same place. Deliberately NOT under
/// the `__trust_wp_reborrow_` prefix, which closure lanes parse structurally.
pub(super) fn nonfinal_reborrow_carrier<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    dest: Local,
    location: Location,
) -> PureExpr {
    PureExpr::Var(
        format!(
            "__trust_wp_nonfinal_rb_{}_{}",
            location.block.as_u32(),
            location.statement_index
        ),
        ty_to_expr_sort_enriched(tcx, body.local_decls[dest].ty),
    )
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
        // The borrowck-only deref of a `Reborrow` type: its own segment, so the
        // reborrow's name never meets a real place's.
        ProjectionElem::PhantomDeref => "phantomderef".to_string(),
    }
}

fn expr_sort(expr: &PureExpr) -> Option<ExprSort> {
    match expr {
        PureExpr::Var(_, sort) => sort.clone(),
        PureExpr::Final(inner) | PureExpr::Old(inner) | PureExpr::View(inner) => expr_sort(inner),
        _ => None,
    }
}
