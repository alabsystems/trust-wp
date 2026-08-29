// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Spanned variant of MIR return expression extraction.
//!
//! Mirrors `extract_from_block_with_context` but threads [`SpannedBodyExpr`]
//! instead of bare `PureExpr` through the recursion for source-span tracking.
//!
//! Phase 3 of #2066: migrated to [`BlockVisitor`] + [`walk_block`] to
//! eliminate duplicated statement dispatch logic.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Location, Operand, Place, Rvalue, StatementKind, TerminatorKind,
    },
    ty::TyCtxt,
};
use rustc_span::Spanned;
use trust_wp_core::formula::{BinOp, PureExpr};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        call_resolve::resolve_arg_names_or_warn,
        effects::CallEffects,
        spanned::SpannedBodyExpr,
        spec_apply::apply_postconditions_with_effects,
        translate::{
            operand_int_ty, operand_is_bool, switch_value_to_expr, translate_operand_detailed,
            ty_to_expr_sort_enriched,
        },
    },
    assertion::{assert_fact_from_condition, wrap_spanned_continuation_with_assert_fact},
    block_visitor::{self, BlockVisitor, VisitorAction},
    call_args::{call_result_symbol, translate_call_args_for_substitutions_with_tcx},
    call_resolve_shared::{classify_cell_builtin_path, resolve_call, ResolvedCallKind},
    extend_call_with_const_generic_args,
    helpers::{rvalue_reads_from_local, translate_rvalue_with_enum_variants},
    try_operator::{self, try_branch_type_is_option},
};

/// Shared context for spanned extraction (spec maps, immutable references).
#[allow(clippy::struct_field_names)] // Mirrors BlockExtractionContext naming convention
struct SpannedExtractionContext<'a> {
    user_specs: &'a HashMap<DefId, StdSpec>,
    trait_specs: &'a HashMap<DefId, StdSpec>,
    extern_specs: &'a HashMap<String, StdSpec>,
}

/// Visitor for the spanned extraction pipeline (Pipeline 2).
///
/// Implements [`BlockVisitor`] to use the shared [`walk_block`] walker,
/// eliminating the duplicated statement dispatch from the previous
/// `extract_from_block_spanned` function. (#2066, Phase 3)
struct SpannedVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    local_exprs: HashMap<Local, SpannedBodyExpr>,
    visited: HashSet<BasicBlock>,
    ctx: &'a SpannedExtractionContext<'a>,
}

impl<'a, 'tcx> BlockVisitor<'tcx> for SpannedVisitor<'a, 'tcx> {
    type Result = SpannedBodyExpr;

    fn visited_mut(&mut self) -> &mut HashSet<BasicBlock> {
        &mut self.visited
    }

    fn on_assign_local(
        &mut self,
        local: Local,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        if let Some(expr) = translate_rvalue_with_enum_variants(
            self.tcx,
            rvalue,
            &self.local_exprs,
            Some(body),
            None,
            Some(location),
        ) {
            // Recover the source span from the statement's source_info.
            let span = body.basic_blocks[location.block].statements[location.statement_index]
                .source_info
                .span;
            self.local_exprs
                .insert(local, SpannedBodyExpr::new(expr, span));
        }
    }

    // on_assign_projected: default no-op (spanned pipeline skips projected writes)
    // on_assign_deref_projected: default no-op
    // check_cutoff_at_statement: default None (no cutoff support)
    // check_cutoff_at_terminator: default None

    fn on_return(&self, _body: &Body<'tcx>) -> Option<Self::Result> {
        self.local_exprs.get(&Local::from_u32(0)).cloned()
    }

    fn on_assert(
        &mut self,
        cond: &Operand<'tcx>,
        expected: bool,
        msg: &rustc_middle::mir::AssertKind<Operand<'tcx>>,
        target: BasicBlock,
        body: &Body<'tcx>,
    ) -> VisitorAction<Self::Result> {
        let fact = assert_fact_from_condition(cond, expected, msg, &self.local_exprs);
        // Take owned state for recursive walk.
        let local_exprs = std::mem::take(&mut self.local_exprs);
        let visited = std::mem::take(&mut self.visited);
        let continuation = extract_from_block_spanned_inner(
            self.tcx,
            body,
            target,
            local_exprs,
            visited,
            self.ctx,
        );
        VisitorAction::Done(wrap_spanned_continuation_with_assert_fact(
            fact,
            continuation,
        ))
    }

    fn on_switch_int(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
        body: &Body<'tcx>,
        bb: BasicBlock,
    ) -> VisitorAction<Self::Result> {
        let local_exprs = std::mem::take(&mut self.local_exprs);
        let visited = std::mem::take(&mut self.visited);
        let terminator = body.basic_blocks[bb].terminator();
        let result = handle_switch_int_spanned(
            self.tcx,
            body,
            discr,
            targets,
            terminator,
            local_exprs,
            visited,
            self.ctx,
        );
        VisitorAction::Done(result)
    }

    fn on_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        target: Option<BasicBlock>,
        body: &Body<'tcx>,
        bb: BasicBlock,
    ) -> VisitorAction<Self::Result> {
        let Some(next_bb) = target else {
            return VisitorAction::bail();
        };
        let terminator = body.basic_blocks[bb].terminator();
        let call_span = terminator.source_info.span;

        let resolved = resolve_call(
            self.tcx,
            body,
            bb,
            func,
            args,
            destination.local,
            self.ctx.user_specs,
            self.ctx.trait_specs,
            self.ctx.extern_specs,
            None,
            &self.local_exprs,
        );
        let cell_builtin = resolved
            .def_id
            .and_then(|def_id| classify_cell_builtin_path(&self.tcx.def_path_str(def_id)));

        let result_expr = if cell_builtin.is_some() {
            PureExpr::Var(
                format!("_call_{}", destination.local.as_u32()),
                ty_to_expr_sort_enriched(self.tcx, body.local_decls[destination.local].ty),
            )
        } else {
            match resolved.kind {
                ResolvedCallKind::ArrayLen(len_expr) => len_expr,
                ResolvedCallKind::DirectSpec(spec) => {
                    let def_id = resolved.def_id.expect("DirectSpec always has def_id");
                    apply_spec_for_spanned(
                        self.tcx,
                        def_id,
                        func,
                        args,
                        &self.local_exprs,
                        body,
                        destination.local,
                        &spec,
                    )
                }
                ResolvedCallKind::ExternSpec(spec) => {
                    let def_id = resolved.def_id.expect("ExternSpec always has def_id");
                    apply_spec_for_spanned(
                        self.tcx,
                        def_id,
                        func,
                        args,
                        &self.local_exprs,
                        body,
                        destination.local,
                        &spec,
                    )
                }
                ResolvedCallKind::BoxNew => {
                    if let Some(arg_expr) = args.first().and_then(|arg| {
                        translate_operand_detailed(&arg.node, &self.local_exprs, None)
                    }) {
                        arg_expr
                    } else {
                        PureExpr::Var(
                            format!("_call_{}", destination.local.as_u32()),
                            ty_to_expr_sort_enriched(
                                self.tcx,
                                body.local_decls[destination.local].ty,
                            ),
                        )
                    }
                }
                ResolvedCallKind::IntPassthrough(int_expr)
                | ResolvedCallKind::LayoutIntrinsic(int_expr) => int_expr,
                ResolvedCallKind::TryBranch => {
                    if let Some(arg_expr) = args.first().and_then(|arg| {
                        translate_operand_detailed(&arg.node, &self.local_exprs, None)
                    }) {
                        if let Some(is_option) = try_branch_type_is_option(self.tcx, func) {
                            if let Some(result) = try_extract_try_operator_spanned(
                                self.tcx,
                                body,
                                is_option,
                                arg_expr,
                                next_bb,
                                destination.local,
                                self.local_exprs.clone(),
                                self.visited.clone(),
                                self.ctx,
                                call_span,
                            ) {
                                return VisitorAction::Done(Some(result));
                            }
                        }
                    }
                    PureExpr::Var(
                        format!("_call_{}", destination.local.as_u32()),
                        ty_to_expr_sort_enriched(self.tcx, body.local_decls[destination.local].ty),
                    )
                }
                ResolvedCallKind::MappingFromClosure
                | ResolvedCallKind::MapInvFromClosure
                | ResolvedCallKind::Opaque => PureExpr::Var(
                    format!("_call_{}", destination.local.as_u32()),
                    ty_to_expr_sort_enriched(self.tcx, body.local_decls[destination.local].ty),
                ),
            }
        };

        self.local_exprs.insert(
            destination.local,
            SpannedBodyExpr::new(result_expr, call_span),
        );
        VisitorAction::Continue(next_bb)
    }
}

/// Extract the return expression with MIR source spans for better error messages.
pub(crate) fn extract_return_expr_spanned<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Option<SpannedBodyExpr> {
    let mut local_exprs: HashMap<Local, SpannedBodyExpr> = HashMap::new();
    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(
            local,
            SpannedBodyExpr::unspanned(PureExpr::Var(name.clone(), sort)),
        );
    }
    let ctx = SpannedExtractionContext {
        user_specs,
        trait_specs,
        extern_specs,
    };
    extract_from_block_spanned_inner(
        tcx,
        body,
        BasicBlock::from_u32(0),
        local_exprs,
        HashSet::new(),
        &ctx,
    )
}

/// Create a [`SpannedVisitor`] and walk the block. Used by both the entry
/// point and recursive calls from visitor callbacks.
fn extract_from_block_spanned_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    local_exprs: HashMap<Local, SpannedBodyExpr>,
    visited: HashSet<BasicBlock>,
    ctx: &SpannedExtractionContext<'_>,
) -> Option<SpannedBodyExpr> {
    let mut visitor = SpannedVisitor {
        tcx,
        local_exprs,
        visited,
        ctx,
    };
    block_visitor::walk_block(body, bb, &mut visitor)
}

#[allow(clippy::too_many_arguments)]
fn try_extract_try_operator_spanned<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    is_option: bool,
    arg_expr: PureExpr,
    next_bb: BasicBlock,
    destination_local: Local,
    mut local_exprs: HashMap<Local, SpannedBodyExpr>,
    mut visited: HashSet<BasicBlock>,
    ctx: &SpannedExtractionContext<'_>,
    call_span: rustc_span::Span,
) -> Option<SpannedBodyExpr> {
    let is_variant_method = if is_option { "is_some" } else { "is_ok" };

    let next_data = &body.basic_blocks[next_bb];
    let term = next_data.terminator();
    let continue_bb = match &term.kind {
        TerminatorKind::SwitchInt { targets, .. } => targets
            .iter()
            .find(|(val, _)| *val == 0)
            .map_or(targets.otherwise(), |(_, bb)| bb),
        TerminatorKind::Goto { target } => {
            let goto_data = &body.basic_blocks[*target];
            match &goto_data.terminator().kind {
                TerminatorKind::SwitchInt { targets, .. } => targets
                    .iter()
                    .find(|(val, _)| *val == 0)
                    .map_or(targets.otherwise(), |(_, bb)| bb),
                _ => return None,
            }
        }
        _ => return None,
    };

    let inner_expr = PureExpr::MethodCall {
        receiver: Arc::new(arg_expr.clone()),
        method: "unwrap".to_string(),
        args: vec![],
    };

    visited.insert(next_bb);

    let continue_data = &body.basic_blocks[continue_bb];
    for stmt in &continue_data.statements {
        if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
            if place.projection.is_empty() {
                if rvalue_reads_from_local(rvalue, destination_local) {
                    local_exprs.insert(
                        place.local,
                        SpannedBodyExpr::new(inner_expr.clone(), stmt.source_info.span),
                    );
                } else if let Some(expr) = translate_rvalue_with_enum_variants(
                    tcx,
                    rvalue,
                    &local_exprs,
                    Some(body),
                    None,
                    None,
                ) {
                    local_exprs.insert(
                        place.local,
                        SpannedBodyExpr::new(expr, stmt.source_info.span),
                    );
                }
            }
        }
    }

    let continue_term = continue_data.terminator();
    let continue_result = match &continue_term.kind {
        TerminatorKind::Goto { target } | TerminatorKind::Drop { target, .. } => {
            extract_from_block_spanned_inner(tcx, body, *target, local_exprs, visited, ctx)
        }
        TerminatorKind::Return => local_exprs.get(&Local::from_u32(0)).cloned(),
        _ => return None,
    };

    // Build Ite(is_some(x) / is_ok(x), continue_body, x) to model
    // both paths of the `?` operator — mirrors try_operator.rs (#2675).
    continue_result.map(|body_expr| {
        // Apply reconstruction optimization: when the continue body wraps
        // `unwrap(x)` back in the same constructor, simplify to `x`.
        // Mirrors try_operator.rs optimization. (#2675)
        let result_expr = if try_operator::is_reconstruction_of(&body_expr.expr, &arg_expr) {
            arg_expr
        } else {
            PureExpr::Ite(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(arg_expr.clone()),
                    method: is_variant_method.to_string(),
                    args: vec![],
                }),
                Arc::new(body_expr.expr),
                Arc::new(arg_expr),
            )
        };
        SpannedBodyExpr::new(result_expr, call_span)
    })
}

/// Handle `SwitchInt` terminators in spanned extraction.
#[allow(clippy::too_many_arguments)]
fn handle_switch_int_spanned<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    discr: &Operand<'tcx>,
    targets: &rustc_middle::mir::SwitchTargets,
    terminator: &rustc_middle::mir::Terminator<'tcx>,
    local_exprs: HashMap<Local, SpannedBodyExpr>,
    visited: HashSet<BasicBlock>,
    ctx: &SpannedExtractionContext<'_>,
) -> Option<SpannedBodyExpr> {
    if targets.all_targets().len() < 2 {
        return None;
    }
    let condition = translate_operand_detailed(discr, &local_exprs, None)?;
    let condition_span = terminator.source_info.span;

    if operand_is_bool(discr, body) {
        let (mut false_bb, mut true_bb) = (None, None);
        for (value, target) in targets.iter() {
            if value == 0 {
                false_bb = Some(target);
            } else if value == 1 {
                true_bb = Some(target);
            }
        }
        let otherwise_bb = targets.otherwise();
        let else_bb = false_bb.unwrap_or(otherwise_bb);
        let then_bb = true_bb.unwrap_or(otherwise_bb);
        if then_bb == else_bb {
            return None;
        }
        let then_s = extract_from_block_spanned_inner(
            tcx,
            body,
            then_bb,
            local_exprs.clone(),
            visited.clone(),
            ctx,
        )?;
        let else_s =
            extract_from_block_spanned_inner(tcx, body, else_bb, local_exprs, visited, ctx)?;
        let ite = PureExpr::Ite(
            Arc::new(condition),
            Arc::new(then_s.expr),
            Arc::new(else_s.expr),
        );
        return Some(SpannedBodyExpr::new(ite, condition_span));
    }

    // General integer switch
    let discr_int_ty = operand_int_ty(discr, body)?;
    let otherwise_s = extract_from_block_spanned_inner(
        tcx,
        body,
        targets.otherwise(),
        local_exprs.clone(),
        visited.clone(),
        ctx,
    )?;
    let mut acc = otherwise_s;
    let mut pairs: Vec<(u128, BasicBlock)> = targets.iter().collect();
    pairs.reverse();
    let last_pair = pairs.pop();
    for (value, target) in pairs {
        let val_expr = switch_value_to_expr(value, discr_int_ty)?;
        let cond = PureExpr::BinOp(Arc::new(condition.clone()), BinOp::Eq, Arc::new(val_expr));
        let branch_s = extract_from_block_spanned_inner(
            tcx,
            body,
            target,
            local_exprs.clone(),
            visited.clone(),
            ctx,
        )?;
        acc = SpannedBodyExpr::new(
            PureExpr::Ite(Arc::new(cond), Arc::new(branch_s.expr), Arc::new(acc.expr)),
            condition_span,
        );
    }
    if let Some((value, target)) = last_pair {
        let val_expr = switch_value_to_expr(value, discr_int_ty)?;
        let cond = PureExpr::BinOp(Arc::new(condition.clone()), BinOp::Eq, Arc::new(val_expr));
        let branch_s =
            extract_from_block_spanned_inner(tcx, body, target, local_exprs, visited, ctx)?;
        acc = SpannedBodyExpr::new(
            PureExpr::Ite(Arc::new(cond), Arc::new(branch_s.expr), Arc::new(acc.expr)),
            condition_span,
        );
    }
    Some(acc)
}

/// Apply a spec for the spanned pipeline: postconditions only, effects dropped.
#[allow(clippy::too_many_arguments)]
fn apply_spec_for_spanned<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_exprs: &HashMap<Local, SpannedBodyExpr>,
    body: &Body<'tcx>,
    destination: Local,
    spec: &StdSpec,
) -> PureExpr {
    let mut translated_args =
        translate_call_args_for_substitutions_with_tcx(args, local_exprs, Some(body), Some(tcx));
    let result_var = call_result_symbol(body, destination, tcx);
    let mut param_names = resolve_arg_names_or_warn(tcx, def_id, spec.param_names.as_ref());
    extend_call_with_const_generic_args(tcx, def_id, func, &mut translated_args, &mut param_names);
    let param_names = (!param_names.is_empty()).then_some(param_names.as_slice());
    let mut effects = CallEffects::new();
    apply_postconditions_with_effects(
        &spec.ensures,
        &result_var,
        &translated_args,
        param_names,
        &mut effects,
        false,
    ) // effects dropped: spanned pass; cleared before main extraction
}
