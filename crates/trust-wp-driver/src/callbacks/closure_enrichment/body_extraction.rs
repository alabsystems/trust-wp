// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure body extraction for inline encoding.
//!
//! Extracts closure MIR bodies as `PureExpr` trees for closures small enough
//! to inline. Also synthesizes capture mutation ensures from MIR write patterns.

use std::{collections::HashMap, sync::Arc};

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{mir::Body, ty::TyCtxt};
use trust_wp_core::{
    closure::{CaptureField, CaptureKind},
    formula::{
        internal::tuple_lowering::{tuple_field_logic_fn_index, tuple_logic_fn_arity},
        BinOp, ExprSort, PureExpr,
    },
};
use trust_wp_driver::StdSpec;

use crate::mir_analysis::{
    extract_return_expr_with_context_detailed, resolve_arg_names_or_warn,
    translate::ty_to_expr_sort_enriched,
};

/// Maximum number of effective basic blocks for closure body inlining.
///
/// Closures with more effective blocks than this threshold fall back to
/// UF+axiom encoding. Matches trust-mc's `inline_translate.rs:40-47` threshold.
/// "Effective" blocks exclude cleanup, resume, and unreachable-only blocks.
const TRUST_WP_CLOSURE_INLINE_BB_THRESHOLD: usize = 6;

/// Count effective basic blocks in a MIR body, excluding cleanup, resume,
/// and unreachable-only blocks.
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

/// Try to extract a closure's body as a `PureExpr` for inline encoding.
///
/// Returns `Some((body_expr, param_names))` if the closure is inlineable:
/// - MIR body is available (same-crate closure)
/// - DefKind is Closure (not inline const)
/// - Body complexity ≤ `TRUST_WP_CLOSURE_INLINE_BB_THRESHOLD` effective basic blocks
/// - `extract_return_expr_with_context` successfully produces an expression
///
/// Returns `None` to fall back to UF+axiom encoding.
pub(in crate::callbacks) fn try_extract_closure_body(
    tcx: TyCtxt<'_>,
    closure_def_id: DefId,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Option<(PureExpr, Vec<String>)> {
    // Only real closures, not inline consts
    if !matches!(tcx.def_kind(closure_def_id), DefKind::Closure) {
        return None;
    }

    // MIR must be available (same-crate)
    if !tcx.is_mir_available(closure_def_id) {
        return None;
    }

    let Ok(closure_body) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tcx.optimized_mir(closure_def_id)
    })) else {
        return None;
    };

    // Complexity gate: only inline simple closures
    let ebb_count = effective_basic_block_count(closure_body);
    if ebb_count > TRUST_WP_CLOSURE_INLINE_BB_THRESHOLD {
        return None;
    }

    // Extract source-level formal parameter names from HIR. Closure body MIR
    // uses `self` followed by the closure parameters as ordinary MIR args.
    let param_names = resolve_arg_names_or_warn(tcx, closure_def_id, None);
    let mir_param_names = closure_mir_arg_names(&param_names);

    // Extract the return expression as a PureExpr
    // Best-effort inline encoding: if body extraction fails the caller falls
    // back to UF+axiom encoding, so diagnostics are intentionally ignored.
    let return_expr = extract_return_expr_with_context_detailed(
        tcx,
        closure_body,
        &mir_param_names,
        user_specs,
        trait_specs,
        extern_specs,
    )
    .value;

    return_expr.map(|expr| (normalize_closure_body_expr(&expr), param_names))
}

fn closure_mir_arg_names(param_names: &[String]) -> Vec<String> {
    let mut mir_param_names = Vec::with_capacity(param_names.len() + 1);
    mir_param_names.push("self".to_string());
    mir_param_names.extend(param_names.iter().cloned());
    mir_param_names
}

fn normalize_closure_body_expr(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            let normalized_args: Vec<_> = args.iter().map(normalize_closure_body_expr).collect();
            if let Some(field_idx) = tuple_field_logic_fn_index(name) {
                if normalized_args.len() == 1 {
                    if let PureExpr::LogicFnCall {
                        name: tuple_name,
                        args: tuple_args,
                    } = &normalized_args[0]
                    {
                        if tuple_logic_fn_arity(tuple_name) == Some(tuple_args.len()) {
                            if let Some(projected) = tuple_args.get(field_idx) {
                                return projected.clone();
                            }
                        }
                    }
                    if field_idx == 0 && can_collapse_scalar_field0(&normalized_args[0]) {
                        return normalized_args[0].clone();
                    }
                }
            }
            PureExpr::LogicFnCall {
                name: name.clone(),
                args: normalized_args,
            }
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(normalize_closure_body_expr(left)),
            *op,
            Arc::new(normalize_closure_body_expr(right)),
        ),
        PureExpr::UnOp(op, inner) => {
            PureExpr::UnOp(*op, Arc::new(normalize_closure_body_expr(inner)))
        }
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(normalize_closure_body_expr(cond)),
            Arc::new(normalize_closure_body_expr(then_expr)),
            Arc::new(normalize_closure_body_expr(else_expr)),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(normalize_closure_body_expr(inner))),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(normalize_closure_body_expr(inner))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(normalize_closure_body_expr(inner))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(normalize_closure_body_expr(inner))),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(normalize_closure_body_expr(receiver)),
            method: method.clone(),
            args: args.iter().map(normalize_closure_body_expr).collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(normalize_closure_body_expr(value)),
            body: Arc::new(normalize_closure_body_expr(body)),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(normalize_closure_body_expr(assumption)),
            body: Arc::new(normalize_closure_body_expr(body)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(normalize_closure_body_expr(obligation)),
            body: Arc::new(normalize_closure_body_expr(body)),
        },
        _ => expr.clone(),
    }
}

fn can_collapse_scalar_field0(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::BinOp(_, _, _) | PureExpr::UnOp(_, _)
    )
}

/// Try to extract a closure body with synthesized capture effect expressions.
///
/// Like `try_extract_closure_body` but also synthesizes ensures expressions for
/// mutable captures by examining projected write facts from the body extraction.
/// For example, `|| { x += 1; 5 }` produces:
/// - body_expr: `Int(5)` (return value)
/// - synthesized ensures: `[Final(Var("x")) == BinOp(Var("x"), Add, Int(1))]`
///
/// The synthesized ensures capture the mutation side effects on mutable captures
/// that body inlining alone cannot represent (#2151 Phase 3).
pub(in crate::callbacks) fn try_extract_closure_body_with_effects(
    tcx: TyCtxt<'_>,
    closure_def_id: DefId,
    capture_fields: &[CaptureField],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Option<(PureExpr, Vec<String>, Option<Vec<PureExpr>>)> {
    if !matches!(tcx.def_kind(closure_def_id), DefKind::Closure) {
        return None;
    }
    if !tcx.is_mir_available(closure_def_id) {
        return None;
    }

    let Ok(closure_body) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tcx.optimized_mir(closure_def_id)
    })) else {
        return None;
    };
    let ebb_count = effective_basic_block_count(closure_body);
    if ebb_count > TRUST_WP_CLOSURE_INLINE_BB_THRESHOLD {
        return None;
    }

    // Use standard body extraction for the return value expression.
    let body_result =
        try_extract_closure_body(tcx, closure_def_id, user_specs, trait_specs, extern_specs);
    let (body_expr, hir_param_names) = body_result?;

    // Synthesize capture mutation ensures by direct MIR analysis.
    // The PrimaryVisitor-based extraction consumes write facts during
    // block transitions, so we walk the MIR directly instead.
    //
    // Pattern: For FnMut closures, `x += 1` compiles to:
    //   _N = copy ((*_1).K: &mut T)   // load capture K's ref
    //   ... compute rhs into _M ...
    //   *_N = move (_M.0: T)           // write through ref
    //
    // We build a local→place map to resolve which capture a deref write
    // targets, then translate the RHS to a PureExpr.
    let mut synthesized_ensures = Vec::new();

    // Build local → capture field index map from copy/move assignments.
    // For `_5 = copy ((*_1).0: &mut u32)`, maps _5 → capture index 0.
    use rustc_middle::mir::{Local as MirLocal, ProjectionElem, Rvalue as MirRvalue};
    let mut local_to_capture: HashMap<MirLocal, usize> = HashMap::new();
    let capture_field_idx = |source_place: &rustc_middle::mir::Place<'_>| -> Option<usize> {
        let projections: &[_] = source_place.projection.as_ref();
        let mut idx = 0;
        while idx < projections.len() && matches!(projections[idx], ProjectionElem::Deref) {
            idx += 1;
        }
        let ProjectionElem::Field(field, _) = projections.get(idx).copied()? else {
            return None;
        };
        if projections[idx + 1..]
            .iter()
            .all(|projection| matches!(*projection, ProjectionElem::Deref))
        {
            Some(field.as_u32() as usize)
        } else {
            None
        }
    };
    let all_deref_projections = |place: &rustc_middle::mir::Place<'_>| {
        let projections: &[_] = place.projection.as_ref();
        !projections.is_empty()
            && projections
                .iter()
                .all(|projection| matches!(*projection, ProjectionElem::Deref))
    };
    for bb_data in closure_body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            if let rustc_middle::mir::StatementKind::Assign((place, rvalue)) = &stmt.kind {
                if !place.projection.is_empty() {
                    continue;
                }
                let (MirRvalue::CopyForDeref(source_place)
                | MirRvalue::Use(
                    rustc_middle::mir::Operand::Copy(source_place)
                    | rustc_middle::mir::Operand::Move(source_place),
                    _,
                )) = rvalue
                else {
                    continue;
                };
                if source_place.local != MirLocal::from_u32(1) {
                    continue;
                }
                if let Some(idx) = capture_field_idx(source_place) {
                    local_to_capture.insert(place.local, idx);
                }
            }
        }
    }
    // Iterate to fixpoint over chained capture propagation. Whole-value
    // rebinds like `let bx2 = bx` (`_N = move _M` with empty projections)
    // and reborrows through derefs both forward capture identity. A single
    // pass misses cases where a later rebind extends an earlier rebind. (09)
    let mut changed = true;
    while changed {
        changed = false;
        for bb_data in closure_body.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                if let rustc_middle::mir::StatementKind::Assign((place, rvalue)) = &stmt.kind {
                    if !place.projection.is_empty() || local_to_capture.contains_key(&place.local) {
                        continue;
                    }
                    let chained_capture = match rvalue {
                        // `_N = move _M` (whole-value rebind, empty projection)
                        // forwards capture identity. Closure body `let bx2 = bx`
                        // compiles to this exact shape, and without it the
                        // deref-write loop below cannot connect `**bx2 = ...`
                        // back to the original capture. (#5 closures/09)
                        MirRvalue::Use(
                            rustc_middle::mir::Operand::Copy(source_place)
                            | rustc_middle::mir::Operand::Move(source_place),
                            _,
                        ) if source_place.projection.is_empty() => {
                            local_to_capture.get(&source_place.local).copied()
                        }
                        MirRvalue::CopyForDeref(source_place)
                        | MirRvalue::Use(
                            rustc_middle::mir::Operand::Copy(source_place)
                            | rustc_middle::mir::Operand::Move(source_place),
                            _,
                        ) if all_deref_projections(source_place) => {
                            local_to_capture.get(&source_place.local).copied()
                        }
                        MirRvalue::Ref(
                            _,
                            rustc_middle::mir::BorrowKind::Mut { .. },
                            source_place,
                        ) if all_deref_projections(source_place) => {
                            local_to_capture.get(&source_place.local).copied()
                        }
                        _ => None,
                    };
                    if let Some(capture_idx) = chained_capture {
                        local_to_capture.insert(place.local, capture_idx);
                        changed = true;
                    }
                }
            }
        }
    }

    // Build local_exprs for RHS translation (needed by translate_rvalue).
    let mut local_exprs: HashMap<MirLocal, PureExpr> = HashMap::new();
    let mut capture_var_sorts: HashMap<usize, Option<ExprSort>> = HashMap::new();
    local_exprs.insert(
        MirLocal::from_u32(1),
        PureExpr::Var(
            "self".to_string(),
            ty_to_expr_sort_enriched(tcx, closure_body.local_decls[MirLocal::from_u32(1)].ty),
        ),
    );
    for (idx, field) in capture_fields.iter().enumerate() {
        for (&local, &capture_idx) in &local_to_capture {
            if capture_idx == idx {
                let local_sort = ty_to_expr_sort_enriched(tcx, closure_body.local_decls[local].ty);
                capture_var_sorts
                    .entry(idx)
                    .or_insert_with(|| local_sort.clone());
                local_exprs.insert(local, PureExpr::Var(field.name().to_string(), local_sort));
            }
        }
    }

    // Process all basic blocks: find deref writes through capture refs.
    // Pattern: *_N = rvalue where _N maps to capture[K]
    use crate::mir_analysis::translate::translate_rvalue;
    for bb_data in closure_body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            if let rustc_middle::mir::StatementKind::Assign((place, rvalue)) = &stmt.kind {
                let projs: Vec<_> = place.projection.iter().collect();
                if !projs.is_empty() && projs.iter().all(|p| matches!(p, ProjectionElem::Deref)) {
                    let Some(&capture_idx) = local_to_capture.get(&place.local) else {
                        continue;
                    };
                    // Try translating the RHS. Fall back to field-0 extraction
                    // for AddWithOverflow results where translate_place can't
                    // project Field(0) on an arithmetic expression.
                    let rhs_expr = translate_rvalue(rvalue, &local_exprs, Some(closure_body))
                        .or_else(|| {
                            let MirRvalue::Use(operand, _) = rvalue else {
                                return None;
                            };
                            let (rustc_middle::mir::Operand::Copy(place)
                            | rustc_middle::mir::Operand::Move(place)) = operand
                            else {
                                return None;
                            };
                            let op_projs: Vec<_> = place.projection.iter().collect();
                            if let [ProjectionElem::Field(f, _)] = op_projs.as_slice() {
                                if f.as_u32() == 0 {
                                    return local_exprs.get(&place.local).cloned();
                                }
                            }
                            None
                        });
                    if let Some(rhs_expr) = rhs_expr {
                        let field = &capture_fields[capture_idx];
                        // Determine ByValue containing &mut (e.g., Box<&mut i32>)
                        // by inspecting the capture's MIR type. The capture lives
                        // at `(*_1).{capture_idx}` in the closure env. (#5 09)
                        let by_value_contains_mut = matches!(field.kind(), CaptureKind::ByValue)
                            && capture_field_eventually_contains_mut_ref(
                                tcx,
                                closure_body,
                                capture_idx,
                            );
                        if matches!(field.kind(), CaptureKind::ByMutRef) || by_value_contains_mut {
                            // RHS capture refs are pre-state values (read at
                            // body entry). Wrap in Old() for substitute_captures_inline
                            // convention: Var(name)=post, Old(Var(name))=pre.
                            let substituted_rhs = substitute_field_to_capture_as_old(
                                &rhs_expr,
                                &format!("self.{capture_idx}"),
                                field.name(),
                            );
                            // For ByValue captures wrapping a mut-ref (e.g.,
                            // `Box<&mut i32>`), the closure body's `**bx = ...`
                            // writes through the inner mut ref. The ensures
                            // models the inner pointee, so wrap both sides in
                            // an extra `Deref` to match the RustHorn final-value
                            // path (`Deref(Old(bx)) + 1` instead of `Old(bx)+1`).
                            let (lhs_expr, rhs_final) = if by_value_contains_mut {
                                (
                                    PureExpr::Deref(Arc::new(PureExpr::Var(
                                        field.name().to_string(),
                                        capture_var_sorts.get(&capture_idx).cloned().flatten(),
                                    ))),
                                    substituted_rhs,
                                )
                            } else {
                                (
                                    PureExpr::Var(
                                        field.name().to_string(),
                                        capture_var_sorts.get(&capture_idx).cloned().flatten(),
                                    ),
                                    substituted_rhs,
                                )
                            };
                            let ensures =
                                PureExpr::BinOp(Arc::new(lhs_expr), BinOp::Eq, Arc::new(rhs_final));
                            synthesized_ensures.push(ensures);
                        }
                    }
                }
            }
            // Track intermediate local assignments for RHS translation context
            if let rustc_middle::mir::StatementKind::Assign((place, rvalue)) = &stmt.kind {
                if place.projection.is_empty() {
                    if let Some(expr) = translate_rvalue(rvalue, &local_exprs, Some(closure_body)) {
                        local_exprs.insert(place.local, expr);
                    }
                }
            }
        }
    }

    let ensures = if synthesized_ensures.is_empty() {
        None
    } else {
        Some(synthesized_ensures)
    };

    Some((body_expr, hir_param_names, ensures))
}

/// Substitute `self.{idx}` variable references with `Old(Var(capture_name))`.
///
/// Used for synthesized ensures RHS where capture values represent the
/// pre-state (read at closure body entry). In the ensures convention,
/// `Old(Var(name))` maps to the pre-state via `substitute_captures_inline`.
fn substitute_field_to_capture_as_old(
    expr: &PureExpr,
    field_name: &str,
    capture_name: &str,
) -> PureExpr {
    match expr {
        PureExpr::Var(name, sort) => {
            if name == field_name || name == capture_name {
                PureExpr::Old(Arc::new(PureExpr::Var(
                    capture_name.to_string(),
                    sort.clone(),
                )))
            } else {
                expr.clone()
            }
        }
        PureExpr::Int(_) | PureExpr::Bool(_) => expr.clone(),
        PureExpr::BinOp(l, op, r) => PureExpr::BinOp(
            Arc::new(substitute_field_to_capture_as_old(
                l,
                field_name,
                capture_name,
            )),
            *op,
            Arc::new(substitute_field_to_capture_as_old(
                r,
                field_name,
                capture_name,
            )),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(substitute_field_to_capture_as_old(
                inner,
                field_name,
                capture_name,
            )),
        ),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(substitute_field_to_capture_as_old(
            inner,
            field_name,
            capture_name,
        ))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(substitute_field_to_capture_as_old(
            inner,
            field_name,
            capture_name,
        ))),
        _ => expr.clone(),
    }
}

/// Determine whether closure capture `capture_idx`'s type eventually contains
/// a `&mut` reference (e.g., `Box<&mut i32>`, `Box<Box<&mut i32>>`).
///
/// Inspects the closure env's `_1` local (which is `&Closure` or `&mut Closure`
/// or the closure itself), peels references, and projects to the capture field.
fn capture_field_eventually_contains_mut_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    closure_body: &Body<'tcx>,
    capture_idx: usize,
) -> bool {
    use rustc_middle::ty::TyKind;
    let env_ty = closure_body.local_decls[rustc_middle::mir::Local::from_u32(1)].ty;
    // Peel any outer references (& Closure, &mut Closure) to reach the closure.
    let mut closure_ty = env_ty;
    while let TyKind::Ref(_, inner, _) = closure_ty.kind() {
        closure_ty = *inner;
    }
    let TyKind::Closure(_, substs) = closure_ty.kind() else {
        return false;
    };
    let upvar_tys = substs.as_closure().upvar_tys();
    let Some(field_ty) = upvar_tys.get(capture_idx) else {
        return false;
    };
    crate::mir_analysis::type_eventually_contains_mut_ref(tcx, *field_ty)
}

/// Whether `name` is `<integer type>::MIN` or `<integer type>::MAX`, the
/// spelling every encoder reads as that constant. A Rust identifier cannot
/// contain `::`, so no formal, capture or temp is spelled this way.
fn is_integer_bound_constant(name: &str) -> bool {
    const INTEGER_TYPES: &[&str] = &[
        "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
    ];
    name.rsplit_once("::")
        .is_some_and(|(ty, bound)| matches!(bound, "MIN" | "MAX") && INTEGER_TYPES.contains(&ty))
}

/// The weakest precondition of a closure's own body, over its formals.
///
/// Returns `(formals, wp)`, or `None` when the WP cannot be computed in full —
/// the body did not extract, a spec clause was dropped, or an obligation names
/// something other than a formal (a capture, a call temp), which no caller-side
/// term denotes. A PARTIAL weakest precondition is strictly weaker than the
/// real one, i.e. a false credit, so there is no partial answer here. An
/// integer type's bound (`isize::MAX`, which a std spec's panic precondition
/// names) is not a name at all: it denotes the same constant on both sides.
///
/// Creusot makes a closure WITHOUT a user contract transparent: its
/// `precondition` predicate is DEFINED as this WP with the argument tuple
/// destructured into the formals — `closure_pre`'s contract-free branch, under
/// a `let` binding the argument tuple. `true` is the one answer that is never
/// right: the callee preconditions the body owes would then be owed by nobody.
pub(in crate::callbacks) fn closure_body_precondition_over_formals(
    tcx: TyCtxt<'_>,
    closure_def_id: DefId,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Option<(Vec<String>, PureExpr)> {
    if !matches!(tcx.def_kind(closure_def_id), DefKind::Closure) {
        return None;
    }
    if !tcx.is_mir_available(closure_def_id) {
        return None;
    }
    let Ok(closure_body) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tcx.optimized_mir(closure_def_id)
    })) else {
        return None;
    };
    if effective_basic_block_count(closure_body) > TRUST_WP_CLOSURE_INLINE_BB_THRESHOLD {
        return None;
    }
    let param_names = resolve_arg_names_or_warn(tcx, closure_def_id, None);
    let mir_param_names = closure_mir_arg_names(&param_names);
    let outcome = crate::mir_analysis::extract_return_expr_with_context_detailed(
        tcx,
        closure_body,
        &mir_param_names,
        user_specs,
        trait_specs,
        extern_specs,
    );
    // Anything the walk could not model, and any clause it had to drop, leaves
    // an obligation list that is only part of what the body owes. A partial
    // weakest precondition is a weaker one, i.e. a false credit.
    if !outcome.diagnostics.entries.is_empty() || outcome.effects.dropped_spec_clauses > 0 {
        return None;
    }
    // A body that returns `()` has no return expression to extract; for any
    // other return type a missing one means the walk stopped short.
    if outcome.value.is_none()
        && !closure_body.local_decls[rustc_middle::mir::Local::from_u32(0)]
            .ty
            .is_unit()
    {
        return None;
    }
    let formals: std::collections::HashSet<&str> = param_names.iter().map(String::as_str).collect();
    let mut conjunction = PureExpr::Bool(true);
    for obligation in &outcome.effects.obligations {
        let mut names_only_formals = true;
        obligation.for_each_recursive(|node| {
            if let PureExpr::Var(name, _) = node {
                names_only_formals &=
                    formals.contains(name.as_str()) || is_integer_bound_constant(name);
            }
        });
        if !names_only_formals {
            return None;
        }
        conjunction = match conjunction {
            PureExpr::Bool(true) => obligation.clone(),
            existing => {
                PureExpr::BinOp(Arc::new(existing), BinOp::And, Arc::new(obligation.clone()))
            }
        };
    }
    Some((param_names, conjunction))
}
