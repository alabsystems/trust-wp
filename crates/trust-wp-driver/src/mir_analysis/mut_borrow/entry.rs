// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local},
    ty::TyCtxt,
};
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
    PureExpr,
};
use trust_wp_driver::StdSpec;

use super::{
    data::{MutBorrowAccumulators, MutBorrowBlockContext, MutBorrowBody, MutBorrowTraversalState},
    extract_mut_borrow_from_block, field_writes,
    finality::{build_delayed_writeback_assumptions, compute_reborrow_metadata, ReborrowMetadata},
    type_analysis::{
        collect_mut_ref_paths_with_tcx, direct_closure_field_seeds, find_mut_borrow_params,
        is_newtype_wrapping_mut, struct_field_count_behind_mut, type_contains_mut_ref_with_tcx,
    },
};
use crate::{
    callbacks::thread_locals::RetainedBorrowckBody,
    mir_analysis::{resolver::compute_resolve_points, translate::ty_to_expr_sort_enriched},
};

/// Build a typed `Deref(Var(name, sort))` expression using MIR type info.
///
/// Shared helper for constructing deref identity expressions with enriched sort
/// metadata from `body.local_decls[local].ty`. Used in both the initial
/// mut-borrow parameter seeding and the `IndexMut` continuation fallback to
/// prevent sort erasure. (#2343)
pub(super) fn make_typed_deref_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
    name: &str,
) -> PureExpr {
    let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
    PureExpr::Deref(Arc::new(PureExpr::Var(name.to_string(), sort)))
}

/// Extract the final value expressions for mutable borrow parameters.
///
/// This function analyzes MIR for functions with `&mut` parameters and
/// extracts how those parameters are modified. It returns a map from
/// parameter name to the expression representing the final value.
///
/// # Example
///
/// For `fn increment_ref(v: &mut i32) { *v += 1; }`:
/// - Input parameter `v: &mut i32`
/// - MIR shows: `*v = *v + 1`
/// - Returns: `{ "v" => BinOp(Deref(Var("v")), Add, Int(1)) }`
///
/// This enables RustHorn-style verification where:
/// - `v_current` = initial value (`*v` at entry)
/// - `v_final` = computed expression evaluated with `v_current`
///
/// # Supported Patterns
///
/// Currently supports:
/// - Simple assignment: `*v = expr`
/// - Compound assignment: `*v += expr`, `*v -= expr`, etc.
/// - Conditional modification: `if cond { *v = a } else { *v = b }`
///
/// Returns `None` if the function is too complex (loops, function calls, etc.)
#[allow(clippy::too_many_lines)]
pub(crate) fn extract_mut_borrow_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    body_with_facts: Option<&RetainedBorrowckBody<'tcx>>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Option<MutBorrowBody> {
    // Check function signature for &mut parameters
    let mut_borrow_params = find_mut_borrow_params(tcx, body, arg_names);
    if mut_borrow_params.is_empty() {
        return None;
    }

    // Build map from Local to symbolic expression, including deref tracking
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    let mut deref_exprs: HashMap<Local, PureExpr> = HashMap::new();
    // Per-field deref tracking for FnMut closure captures.
    // Key: (local, field_index), e.g., (_1, 0) for `(*_1).0`.
    let mut field_deref_exprs: HashMap<(Local, u32), PureExpr> = HashMap::new();

    // Initialize arguments with their names, populating ExprSort from MIR types (#1965).
    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort.clone()));

        // For mutable borrow params, initialize deref tracking
        // *v maps to Deref(Var("v")) which encodes as v_current
        if mut_borrow_params.contains(&local) {
            let base_deref_expr = make_typed_deref_expr(tcx, body, local, name);
            deref_exprs.insert(local, base_deref_expr.clone());

            // For closure env parameters (named "self"), initialize per-field
            // tracking for captured variables. Captured fields are accessed as
            // `(*_1).0`, `(*_1).1`, etc. in MIR.
            if name == "self" {
                for seed in direct_closure_field_seeds(tcx, body, local) {
                    let field_name = format!("self.{}", seed.field_idx);
                    field_deref_exprs.insert(
                        (local, seed.field_idx),
                        PureExpr::Deref(Arc::new(PureExpr::Var(field_name, seed.sort))),
                    );
                }
            } else {
                // For composite non-closure parameters containing inner `&mut`
                // fields (e.g., tuple/newtype wrappers), seed identity tracking
                // for one-level field projections.
                //
                // Example:
                //   p: (&mut T, &mut U)   -> p.0, p.1
                //   b: &mut (i32, &mut i32) -> b.1
                //
                // These seeded entries are authoritative when no writes occur.
                let local_ty = body.local_decls[local].ty;
                for path in collect_mut_ref_paths_with_tcx(tcx, local_ty) {
                    if let [field_idx] = path.as_slice() {
                        let field_ref_expr = PureExpr::LogicFnCall {
                            name: tuple_field_logic_fn_name(*field_idx as usize),
                            args: vec![base_deref_expr.clone()],
                        };
                        field_deref_exprs.insert(
                            (local, *field_idx),
                            PureExpr::Deref(Arc::new(field_ref_expr)),
                        );
                    }
                }
            }
        }
    }

    // Mutable accumulators threaded through extraction (#2166).
    let mut accum = MutBorrowAccumulators {
        indexed_writes: Vec::new(),
        mutation_continued_params: HashSet::new(),
        pending_index_mut: HashMap::new(),
        nested_transfer_slots: HashSet::new(),
        nested_transfer_poisoned: false,
        havoc_params: HashSet::new(),
        carrier_written_fields: HashSet::new(),
        field_written_params: HashSet::new(),
        whole_written_params: HashSet::new(),
        held_pointee_written_params: HashSet::new(),
    };

    // Borrows lent into the return value (see `lent.rs`).
    let lent_analysis = super::lent::analyze_lent_borrows(tcx, body);
    let mut borrow_taint: HashMap<Local, HashSet<Local>> = HashMap::new();
    for arg in body.args_iter() {
        borrow_taint.insert(arg, HashSet::from([arg]));
    }

    // Extract final values through block traversal
    let ctx = MutBorrowBlockContext {
        tcx,
        body,
        mut_borrow_params: &mut_borrow_params,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        borrow_carrying: &lent_analysis.carries,
    };
    let state = MutBorrowTraversalState {
        local_exprs,
        deref_exprs,
        field_deref_exprs,
        reborrow_map: HashMap::new(),
        field_reborrow_map: HashMap::new(),
        slice_reborrow_map: HashMap::new(),
        slot_borrow_map: HashMap::new(),
        slot_alias_roots: HashMap::new(),
        slot_exprs: HashMap::new(),
        carrier_field_reborrows: HashMap::new(),
        carrier_read_locals: mut_borrow_params
            .iter()
            .copied()
            .filter(|local| {
                field_writes::value_carrier_referent(tcx, body.local_decls[*local].ty).is_some()
            })
            .collect(),
        visited: HashSet::new(),
        borrow_taint,
    };
    let (final_deref_exprs, final_field_deref_exprs, final_slot_exprs) =
        extract_mut_borrow_from_block(&ctx, BasicBlock::from_u32(0), state, &mut accum)?;

    // Params marked lent on some path by the traversal replay must be treated
    // as lent even if the flow-insensitive pass (an over-approximation that
    // should already contain them) disagreed.
    let mut lent_locals: HashSet<Local> = lent_analysis.lent.clone();
    for (local, expr) in &final_deref_exprs {
        if expr_contains_lent_marker(expr) {
            lent_locals.insert(*local);
        }
    }
    let mut lent_path_resolutions: Vec<PureExpr> = Vec::new();
    if lent_analysis.refinable {
        let mut locals: Vec<Local> = lent_locals.iter().copied().collect();
        locals.sort();
        for local in locals {
            let Some(param_idx) = local.as_usize().checked_sub(1) else {
                continue;
            };
            let Some(name) = arg_names.get(param_idx) else {
                continue;
            };
            // A param already mutation-continued for another reason has no
            // trusted exit pointee: its final_values entry would have been
            // gated off, so no path-restricted copy of it may be asserted.
            if name == "self"
                || accum.mutation_continued_params.contains(name)
                || is_newtype_wrapping_mut(tcx, body.local_decls[local].ty)
                || accum.nested_transfer_slots.contains(&local)
                || final_field_deref_exprs.keys().any(|(l, _)| *l == local)
            {
                continue;
            }
            let Some(tree) = final_deref_exprs.get(&local) else {
                continue;
            };
            let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
            let prophecy = PureExpr::Final(Arc::new(PureExpr::Var(name.clone(), sort)));
            let mut out = Vec::new();
            if collect_unlent_path_resolutions(tree, &prophecy, &mut Vec::new(), &mut out) {
                lent_path_resolutions.extend(out);
            }
        }
    }

    // Build result map from parameter name to final value
    let mut final_values = HashMap::new();
    for (local, final_expr) in final_deref_exprs {
        let param_idx = local.as_usize().checked_sub(1)?;
        if param_idx < arg_names.len() {
            // Skip whole-deref entries for closure env params that have
            // field-level tracking (the per-field entries are authoritative).
            if arg_names[param_idx] == "self" && !final_field_deref_exprs.is_empty() {
                continue;
            }
            // For newtype parameters (single-field ADTs wrapping &mut), wrap the
            // inner deref value in a tuple constructor. Postconditions like `^x.0`
            // parse as `Final(tuple_get_0(Var("x")))`, so the final value must be
            // a tuple-like value that the tuple axiom `tuple_get_0(tuple1(v)) = v`
            // can decompose. Without the wrapper, x_final = 5 (bare int) and
            // tuple_get_0(5) is uninterpreted -> spurious failure.
            let local_decl = &body.local_decls[local];
            let wrapped = if is_newtype_wrapping_mut(tcx, local_decl.ty) {
                PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(1),
                    args: vec![final_expr],
                }
            } else {
                final_expr
            };
            final_values.insert(arg_names[param_idx].clone(), wrapped);
        }
    }

    populate_field_and_newtype_final_values(
        tcx,
        body,
        arg_names,
        &final_field_deref_exprs,
        &mut final_values,
    )?;

    // The value a `&mut` parameter is left with must reflect every write to
    // its referent, or no premise may state it (D-184):
    // (1) a write THROUGH a borrow the referent holds (`*x.m = 5`) leaves `x`
    //     holding that borrow with a new current value, which the per-field
    //     reconstruction cannot state at the field's sort (it would put the
    //     pointee `5` where the borrow is);
    // (2) a per-field write the reconstruction above did not reach `^x` with
    //     leaves the entry identity `*x`, which would make the write
    //     invisible to every clause reading a field of `^x` (`(^x).m`, or
    //     `x.m` as the value `x` is left with).
    // Either way the entry stays as the declaration carrier and loses its
    // force, as a by-value carrier's does below.
    let mut forceless: Vec<(Local, String)> = final_field_deref_exprs
        .keys()
        .map(|&(local, _)| local)
        .chain(accum.held_pointee_written_params.iter().copied())
        .filter_map(|local| {
            let name = arg_names.get(local.as_usize().checked_sub(1)?)?;
            let is_mut_ref = matches!(
                body.local_decls[local].ty.kind(),
                rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
            );
            let unreconstructed = final_values
                .get(name)
                .is_some_and(|whole| field_writes::is_identity_deref(name, whole));
            (is_mut_ref && (accum.held_pointee_written_params.contains(&local) || unreconstructed))
                .then(|| (local, name.clone()))
        })
        .collect();
    forceless.sort();
    forceless.dedup();
    for (local, name) in forceless {
        if final_values.contains_key(&name) {
            final_values.insert(name.clone(), make_typed_deref_expr(tcx, body, local, &name));
        }
        accum.mutation_continued_params.insert(name);
    }

    // Value carriers (s34): per-field final entries for written top-level
    // fields, projected from the whole final value (literal consequences).
    let mut carrier_fields: HashMap<Local, Vec<u32>> = HashMap::new();
    for &(local, idx) in &accum.carrier_written_fields {
        carrier_fields.entry(local).or_default().push(idx);
    }
    for (local, mut idxs) in carrier_fields {
        if accum.havoc_params.contains(&local) {
            continue;
        }
        let Some(name) = local
            .as_usize()
            .checked_sub(1)
            .and_then(|idx| arg_names.get(idx))
        else {
            continue;
        };
        let Some(whole) = final_values.get(name).cloned() else {
            continue;
        };
        if field_writes::is_identity_deref(name, &whole) {
            continue;
        }
        idxs.sort_unstable();
        idxs.dedup();
        final_values.extend(field_writes::carrier_field_final_entries(
            name, &whole, idxs,
        ));
    }

    // A BY-VALUE carrier of `&mut` fields gets no whole-carrier final value.
    //
    // The identity `^p == *p` is true of the tuple's own value — a pair of
    // references nothing reassigns — but the encoder reads a field back out of
    // that carrier with `tuple_get_N` at the sort of the REFERENT, so the
    // identity descends as `^p.N == *p.N` for every field. That is asserted
    // about a function that writes THROUGH those fields, in both directions at
    // once: the write becomes invisible, and the true post-state is refuted by
    // the same equality. The per-field entries below the carrier are the ones
    // that name a place with a prophecy; a clause this leaves unprovable loses
    // a premise, which is the direction to lose in.
    //
    // A newtype carrier keeps its entry: its final value is the referent's
    // POST-write value wrapped in a constructor, not an identity, so nothing
    // descends that contradicts the write.
    let mut byvalue_carriers: Vec<String> = Vec::new();
    for (idx, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(idx + 1);
        if accum.havoc_params.contains(&local) {
            continue;
        }
        let ty = body.local_decls[local].ty;
        if matches!(
            ty.kind(),
            rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
        ) || !type_contains_mut_ref_with_tcx(tcx, ty)
        {
            continue;
        }
        if final_values
            .get(name)
            .is_some_and(|whole| field_writes::is_identity_deref(name, whole))
        {
            byvalue_carriers.push(name.clone());
        }
    }
    for name in byvalue_carriers {
        // The entry stays as the DECLARATION carrier the ay layer expects —
        // the per-field entries are written in terms of it, and dropping it
        // outright leaves them projecting out of an unbound symbol at the
        // wrong sort. What goes is its force: a mutation-continued param has
        // its `_current_final` alias tied to its own final symbol instead of
        // to its entry value, and gets no identity resolve either, so nothing
        // descends to the fields.
        accum.mutation_continued_params.insert(name);
    }

    // Havocked params (s34): the referent could not be tracked exactly. Remove
    // every final-value premise (whole, per-field, indexed writes) and mark the
    // param mutation-continued so the ay layer asserts neither the final value
    // nor the identity resolve. The identity entry is kept only as the
    // declaration carrier the ay layer expects for continued params.
    let mut havoc_locals: Vec<Local> = accum.havoc_params.iter().copied().collect();
    havoc_locals.sort();
    for local in havoc_locals {
        let Some(name) = local
            .as_usize()
            .checked_sub(1)
            .and_then(|idx| arg_names.get(idx))
            .cloned()
        else {
            continue;
        };
        let field_prefix = format!("{name}.");
        final_values.retain(|key, _| key != &name && !key.starts_with(&field_prefix));
        let identity = make_typed_deref_expr(tcx, body, local, &name);
        let identity = if is_newtype_wrapping_mut(tcx, body.local_decls[local].ty) {
            PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(1),
                args: vec![identity],
            }
        } else {
            identity
        };
        final_values.insert(name.clone(), identity);
        accum
            .indexed_writes
            .retain(|write| write.param_name != name);
        accum.mutation_continued_params.insert(name);
    }

    // Borrows lent into the return value (soundness). A `&mut` parameter
    // whose borrow — whole, a field reborrow, a deeper reborrow, or inside an
    // aggregate — may flow into `RETURN_PLACE` on ANY path keeps being written
    // by the caller through `result`, so every `final_values` entry for it
    // (identity, branch-merged identity, or field reconstruction) is a FALSE
    // premise. Remove them all and treat the param as mutation-continued, so
    // neither `^p == <entry>` nor an identity resolve is asserted. Only
    // premises are deleted.
    let lent_param_names: Vec<String> = {
        let mut names: Vec<String> = lent_locals
            .iter()
            .copied()
            .filter_map(|local| {
                let idx = local.as_usize().checked_sub(1)?;
                arg_names.get(idx).cloned()
            })
            .collect();
        names.sort();
        names
    };
    for name in &lent_param_names {
        let field_prefix = format!("{name}.");
        final_values.retain(|key, _| key != name && !key.starts_with(&field_prefix));
        accum.mutation_continued_params.insert(name.clone());
    }

    // Nested-reborrow transfer resolutions (rusthorn inc_max_3 class).
    //
    // For each parameter slot rebound by a recognized transfer call, emit the
    // RustHorn expiry resolution `Final(<content>) == <value>`: the borrow
    // actually residing in the slot at exit (`<content>`, branch-merged over
    // the slots' entry borrows) resolves to the slot's pointee value at exit.
    // The slot's own `final_values` identity entry — which would wrongly pin
    // the prophecy of the slot's ENTRY borrow to the slot's exit value — is
    // removed, and the param joins `mutation_continued_params` so no identity
    // resolve (`p_final == p_current`) is emitted either.
    //
    // Poisoned or incomplete tracking keeps the suppressions but emits no
    // resolutions (fail-closed: under-constrained, never mis-constrained).
    let mut nested_slot_resolutions: Vec<PureExpr> = Vec::new();
    let mut nested_transfer_params: HashSet<String> = HashSet::new();
    if !accum.nested_transfer_slots.is_empty() {
        let mut slots: Vec<Local> = accum.nested_transfer_slots.iter().copied().collect();
        slots.sort();
        for slot in slots {
            let Some(param_idx) = slot.as_usize().checked_sub(1) else {
                continue;
            };
            let name = arg_names
                .get(param_idx)
                .cloned()
                .unwrap_or_else(|| format!("$param_{}", slot.as_u32()));
            let removed_value = final_values.remove(&name);
            accum.mutation_continued_params.insert(name.clone());
            nested_transfer_params.insert(name.clone());
            if accum.nested_transfer_poisoned {
                continue;
            }
            let (Some(content), Some(value)) = (final_slot_exprs.get(&slot), removed_value) else {
                // Slot content or exit value missing — treat like poison for
                // the whole feature (a partial resolution set could combine
                // with the suppressions to under- or mis-constrain siblings).
                nested_slot_resolutions.clear();
                accum.nested_transfer_poisoned = true;
                continue;
            };
            // Flatten the branch-merged Ite trees into per-path guarded
            // implications `g1 && .. && gk ==> Final(<entry borrow>) == <value>`.
            // Logically equivalent to the single Ite equality, but each premise
            // is a ground clause over the branch atoms — no ite-expansion aux
            // variables in the solver encoding (the nested-ite form made ay
            // orders of magnitude slower than the clausal form).
            flatten_slot_resolution(
                content,
                &value,
                &mut Vec::new(),
                &mut nested_slot_resolutions,
            );
        }
        if accum.nested_transfer_poisoned {
            nested_slot_resolutions.clear();
        }
    }

    // A lent borrow may be the content of a transfer slot (or the slot
    // itself): its expiry resolution would pin a prophecy the caller owns.
    if !lent_param_names.is_empty() {
        nested_slot_resolutions.clear();
        if !nested_transfer_params.is_empty() {
            lent_path_resolutions.clear();
        }
    }

    // Drain accumulators (#2166).
    let indexed_writes = accum.indexed_writes;
    let mutation_continued_params = accum.mutation_continued_params;

    // Compute dataflow-precise resolve points (#2150 Phase 2).
    let resolve_results = Some(compute_resolve_points(
        tcx,
        body,
        arg_names,
        body_with_facts,
    ));

    let ReborrowMetadata {
        finality,
        borrow_id_origins,
    } = compute_reborrow_metadata(tcx, body, arg_names);
    let delayed_writeback_assumptions = resolve_results
        .as_ref()
        .map(|results| build_delayed_writeback_assumptions(&results.writebacks, &finality))
        .unwrap_or_default();

    Some(MutBorrowBody {
        final_values,
        indexed_writes,
        resolve_results,
        finality,
        borrow_id_origins,
        delayed_writeback_assumptions,
        mutation_continued_params,
        nested_slot_resolutions,
        nested_transfer_params,
        lent_path_resolutions,
    })
}

fn expr_contains_lent_marker(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| {
        matches!(node, PureExpr::LogicFnCall { name, .. } if name == super::lent::LENT_ON_PATH_MARKER)
    })
}

/// Walk a branch-merged final pointee tree of a param lent on SOME path and
/// emit `guards ==> Final(p) == leaf` for every leaf NOT wrapped in the lent
/// marker: on that path the borrow is dropped (not returned) at exit with
/// pointee `leaf`, which is exactly its RustHorn resolution. Marked leaves
/// (returned on that path) emit nothing. Returns false — emit nothing for this
/// param at all — if a marker occurs anywhere but as a whole leaf.
fn collect_unlent_path_resolutions(
    tree: &PureExpr,
    prophecy: &PureExpr,
    guards: &mut Vec<PureExpr>,
    out: &mut Vec<PureExpr>,
) -> bool {
    use trust_wp_core::formula::{BinOp, UnOp};

    const MAX_GUARD_DEPTH: usize = 8;
    match tree {
        PureExpr::Ite(cond, then_branch, else_branch) => {
            if guards.len() >= MAX_GUARD_DEPTH || expr_contains_lent_marker(cond) {
                return false;
            }
            guards.push(cond.as_ref().clone());
            let then_ok = collect_unlent_path_resolutions(then_branch, prophecy, guards, out);
            guards.pop();
            guards.push(PureExpr::UnOp(UnOp::Not, Arc::clone(cond)));
            let else_ok = collect_unlent_path_resolutions(else_branch, prophecy, guards, out);
            guards.pop();
            then_ok && else_ok
        }
        PureExpr::LogicFnCall { name, .. } if name == super::lent::LENT_ON_PATH_MARKER => true,
        leaf => {
            if expr_contains_lent_marker(leaf) {
                return false;
            }
            let eq = PureExpr::BinOp(
                Arc::new(prophecy.clone()),
                BinOp::Eq,
                Arc::new(leaf.clone()),
            );
            let Some(first) = guards.first().cloned() else {
                out.push(eq);
                return true;
            };
            let antecedent = guards.iter().skip(1).cloned().fold(first, |acc, g| {
                PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(g))
            });
            out.push(PureExpr::BinOp(
                Arc::new(antecedent),
                BinOp::Implies,
                Arc::new(eq),
            ));
            true
        }
    }
}

/// Flatten a nested-slot expiry resolution `Final(<content>) == <value>` into
/// per-path guarded implications.
///
/// `content` and `value` are branch-merged `Ite` trees over the same branch
/// conditions (the content tree may be shallower where a merge deduplicated
/// identical arms). Splitting is lockstep when both trees branch on the same
/// condition, single-sided otherwise. Leaves emit
/// `guards ==> (Final(content_leaf) == value_leaf)` — logically equivalent to
/// the unflattened Ite equality (sound both ways), but clausal for the solver.
fn flatten_slot_resolution(
    content: &PureExpr,
    value: &PureExpr,
    guards: &mut Vec<PureExpr>,
    out: &mut Vec<PureExpr>,
) {
    use trust_wp_core::formula::{BinOp, UnOp};

    // Path explosion guard: beyond this depth, emit the unflattened Ite
    // equality for the remaining subtree (still exact).
    const MAX_GUARD_DEPTH: usize = 8;

    let split = |cond: &Arc<PureExpr>,
                 arms: [(&PureExpr, &PureExpr); 2],
                 guards: &mut Vec<PureExpr>,
                 out: &mut Vec<PureExpr>| {
        let [(then_c, then_v), (else_c, else_v)] = arms;
        guards.push(cond.as_ref().clone());
        flatten_slot_resolution(then_c, then_v, guards, out);
        guards.pop();
        guards.push(PureExpr::UnOp(UnOp::Not, Arc::clone(cond)));
        flatten_slot_resolution(else_c, else_v, guards, out);
        guards.pop();
    };

    if guards.len() < MAX_GUARD_DEPTH {
        match (content, value) {
            (PureExpr::Ite(c1, t1, e1), PureExpr::Ite(c2, t2, e2)) if c1 == c2 => {
                split(c1, [(t1, t2), (e1, e2)], guards, out);
                return;
            }
            (_, PureExpr::Ite(c2, t2, e2)) => {
                split(c2, [(content, t2), (content, e2)], guards, out);
                return;
            }
            (PureExpr::Ite(c1, t1, e1), _) => {
                split(c1, [(t1, value), (e1, value)], guards, out);
                return;
            }
            _ => {}
        }
    }

    let eq = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(content.clone()))),
        BinOp::Eq,
        Arc::new(value.clone()),
    );
    if guards.is_empty() {
        out.push(eq);
        return;
    }
    let mut it = guards.iter().cloned();
    let first = it.next().expect("non-empty guards");
    let antecedent = it.fold(first, |acc, g| {
        PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(g))
    });
    out.push(PureExpr::BinOp(
        Arc::new(antecedent),
        BinOp::Implies,
        Arc::new(eq),
    ));
}

/// Populate per-field and newtype-reconstructed final values from field deref exprs.
///
/// Three-phase process:
/// 1. Add per-field final values (e.g., "x.0", "self.0") for all parameters.
/// 2. For newtypes wrapping `&mut T`, reconstruct whole-param values from field
///    updates. When `HasMutRef(pub &'a mut T)` has `field_deref[(_1, 0)] = Int(5)`
///    but `final_values["x"]` still holds the identity, this reconstructs
///    `x_final = tuple1(5)`.
/// 3. For structs/tuples behind `&mut` with field-level writes, reconstruct
///    whole-struct final values from per-field finals (#2683), one-field
///    referents included (D-184).
fn populate_field_and_newtype_final_values<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    final_field_deref_exprs: &HashMap<(Local, u32), PureExpr>,
    final_values: &mut HashMap<String, PureExpr>,
) -> Option<()> {
    // Phase 1: per-field values ("self.0", "_x.0", "b.1")
    for ((local, field_idx), final_expr) in final_field_deref_exprs {
        let param_idx = local.as_usize().checked_sub(1)?;
        if param_idx < arg_names.len() {
            final_values.insert(
                format!("{}.{field_idx}", arg_names[param_idx]),
                final_expr.clone(),
            );
        }
    }

    // Phase 2: reconstruct whole-param from field updates for newtypes
    for &(local, _field_idx) in final_field_deref_exprs.keys() {
        let Some(param_idx) = local.as_usize().checked_sub(1) else {
            continue;
        };
        if param_idx >= arg_names.len() {
            continue;
        }
        let local_decl = &body.local_decls[local];
        if !is_newtype_wrapping_mut(tcx, local_decl.ty) {
            continue;
        }
        if let Some(field_val) = final_field_deref_exprs.get(&(local, 0)) {
            let reconstructed = PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(1),
                args: vec![field_val.clone()],
            };
            final_values.insert(arg_names[param_idx].clone(), reconstructed);
        }
    }

    // Phase 3 (#2683): reconstruct whole-struct final values for structs and
    // tuples behind &mut, a one-field referent included (D-184).
    //
    // When a function writes to individual fields of a &mut struct parameter
    // (e.g., `x.a = 34` on `&mut S { a, b }`), the per-field final values are
    // tracked correctly but the whole-struct final value remains the identity
    // `Deref(Var("x"))`. This disconnects the struct-level final (used in type
    // invariant postconditions like `(^x).invariant()`) from the field writes.
    //
    // Fix: reconstruct `x_final = tupleN(field0_final, field1_final, ...)`
    // where written fields use their tracked final value and unwritten fields
    // use `tuple_get_N(Deref(Var(param)))` (the identity/unchanged value).
    let mut seen_locals: HashSet<Local> = HashSet::new();
    for &(local, _) in final_field_deref_exprs.keys() {
        if !seen_locals.insert(local) {
            continue;
        }
        let Some(param_idx) = local.as_usize().checked_sub(1) else {
            continue;
        };
        if param_idx >= arg_names.len() {
            continue;
        }
        let local_decl = &body.local_decls[local];
        // Skip newtypes (handled in Phase 2) and closure envs
        if is_newtype_wrapping_mut(tcx, local_decl.ty) {
            continue;
        }
        if arg_names[param_idx] == "self" {
            continue;
        }
        let Some(field_count) = struct_field_count_behind_mut(tcx, local_decl.ty) else {
            continue;
        };
        let param_name = &arg_names[param_idx];
        let sort = crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, local_decl.ty);
        let base_deref = PureExpr::Deref(Arc::new(PureExpr::Var(param_name.clone(), sort)));
        let mut field_args = Vec::with_capacity(field_count);
        for field_idx in 0..field_count {
            let field_idx_u32 = field_idx as u32;
            if let Some(field_final) = final_field_deref_exprs.get(&(local, field_idx_u32)) {
                field_args.push(field_final.clone());
            } else {
                // Unwritten field: identity from base deref
                field_args.push(PureExpr::LogicFnCall {
                    name: tuple_field_logic_fn_name(field_idx),
                    args: vec![base_deref.clone()],
                });
            }
        }
        let reconstructed = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(field_count),
            args: field_args,
        };
        final_values.insert(param_name.clone(), reconstructed);
    }

    Some(())
}
