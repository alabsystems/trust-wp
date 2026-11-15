// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Location},
    ty::TyCtxt,
};
use rustc_span::Span;
use trust_wp_core::formula::{ExprSort, MatchArm, PureExpr};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        diagnostics::{ExtractionDiagnosticSink, ExtractionOutcome},
        effects::CallEffects,
        loops::detect_loops,
        translate::ty_to_expr_sort_enriched,
    },
    extract_from_block_with_context, BlockExtractionContext, NameSubstitutions,
};

/// Configuration for a single extraction pass.
///
/// Bundles the scoping, cutoff, and diagnostics parameters that control
/// how [`extract_return_expr_impl`] behaves, keeping the function under
/// clippy's `too_many_arguments` threshold. (#2657)
pub(in crate::mir_analysis) struct ExtractionConfig<'a> {
    pub(in crate::mir_analysis) scope_call_context: bool,
    pub(in crate::mir_analysis) cutoff_span: Option<Span>,
    pub(in crate::mir_analysis) cutoff_location: Option<Location>,
    pub(in crate::mir_analysis) diagnostics: Option<&'a ExtractionDiagnosticSink>,
}

/// Extract the return expression from a function's MIR, with `TyCtxt` for function call support.
///
/// This enhanced version can handle simple function calls by looking up specs
/// in trust-wp-std. When a call to a known std function is encountered, the
/// postconditions are used to model the return value.
///
/// # Arguments
/// * `tcx` - Type context for resolving function paths
/// * `body` - The MIR body to analyze
/// * `arg_names` - Names of function arguments for symbolic representation
///
/// # Returns
/// `Some(PureExpr)` if extraction succeeds, `None` if too complex
///
/// # Note
/// This function requires access to `TyCtxt` for resolving function calls
/// against user specs and standard library specifications.
pub(crate) fn extract_return_expr_with_context_detailed<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> ExtractionOutcome<PureExpr> {
    let diagnostics = ExtractionDiagnosticSink::default();
    let config = ExtractionConfig {
        scope_call_context: false,
        cutoff_span: None,
        cutoff_location: None,
        diagnostics: Some(&diagnostics),
    };
    let (value, effects) = extract_return_expr_impl(
        tcx,
        body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        config,
    );
    ExtractionOutcome {
        value,
        effects,
        diagnostics: diagnostics.into_inner(),
    }
}

#[cfg(test)]
pub(crate) fn extract_return_expr_with_context<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> (Option<PureExpr>, CallEffects) {
    let config = ExtractionConfig {
        scope_call_context: false,
        cutoff_span: None,
        cutoff_location: None,
        diagnostics: None,
    };
    extract_return_expr_impl(
        tcx,
        body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        config,
    )
}

/// Extract a scoped MIR expression up to (but excluding) a MIR location.
///
/// This is the location-precise variant used by `proof_assert!` snapshots.
pub(crate) fn extract_return_expr_scoped_until_location_detailed<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    stop_location: Location,
) -> ExtractionOutcome<PureExpr> {
    let diagnostics = ExtractionDiagnosticSink::default();
    let config = ExtractionConfig {
        scope_call_context: true,
        cutoff_span: None,
        cutoff_location: Some(stop_location),
        diagnostics: Some(&diagnostics),
    };
    let (value, effects) = extract_return_expr_impl(
        tcx,
        body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        config,
    );
    ExtractionOutcome {
        value,
        effects,
        diagnostics: diagnostics.into_inner(),
    }
}

/// Core extraction implementation.
///
/// Accepts an [`ExtractionConfig`] to bundle scoping/cutoff/diagnostics
/// parameters, keeping the argument count under clippy's threshold. (#2657)
pub(in crate::mir_analysis) fn extract_return_expr_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    config: ExtractionConfig<'_>,
) -> (Option<PureExpr>, CallEffects) {
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
    }
    let visited = HashSet::new();
    // Run loop detection so the extraction pipeline can skip inner loop
    // bodies instead of hitting ControlFlowCycle on back-edges. (#2698)
    let loop_analysis = detect_loops(body);
    let loop_ref = if loop_analysis.has_loops {
        Some(&loop_analysis)
    } else {
        None
    };
    let ctx = BlockExtractionContext {
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        scope_call_context: config.scope_call_context,
        cutoff_span: config.cutoff_span,
        cutoff_location: config.cutoff_location,
        diagnostics: config.diagnostics,
        loop_analysis: loop_ref,
        skipped_loop_merges: std::cell::OnceCell::new(),
    };
    let mut block_effects = CallEffects::new();
    // Per-borrow prophecy carriers for locally-rooted borrows (#124): one
    // registry per extraction pass. Carrier minting and chain advancement
    // happen at mutating call sites (spec resolution); the expiry-resolution
    // facts `^carrier == <death value>` are collected here at walk end.
    super::borrow_carriers::begin_extraction_pass(tcx, body);
    let result = extract_from_block_with_context(
        tcx,
        body,
        BasicBlock::from_u32(0),
        local_exprs,
        visited,
        &ctx,
        &mut block_effects,
    );
    let expiry_facts = super::borrow_carriers::end_extraction_pass();
    // Expiry resolution is only sound at the borrow's genuine death. A
    // cutoff pass stops MID-function (proof_assert snapshots), where the
    // tracked borrows may still be live — never emit there. An incomplete
    // walk (no result) has incomplete tracking — never emit there either.
    if config.cutoff_span.is_none() && config.cutoff_location.is_none() && result.is_some() {
        block_effects.assumptions.extend(expiry_facts);
    }
    (result, block_effects)
}

pub(crate) fn normalize_immutable_ref_param_derefs<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
) -> impl Fn(&PureExpr) -> PureExpr {
    let mut aliases = HashMap::new();
    for (index, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(index + 1);
        let Some(decl) = body.local_decls.get(local) else {
            continue;
        };
        let rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not) = decl.ty.kind()
        else {
            continue;
        };
        let Some(ExprSort::Ref(inner_sort)) = ty_to_expr_sort_enriched(tcx, decl.ty) else {
            continue;
        };
        aliases.insert(name.clone(), (*inner_sort).clone());
    }
    move |expr| normalize_immutable_ref_deref_expr(expr, &aliases)
}

fn normalize_immutable_ref_deref_expr(
    expr: &PureExpr,
    aliases: &HashMap<String, ExprSort>,
) -> PureExpr {
    match expr {
        PureExpr::Var(name, Some(ExprSort::Ref(_))) => {
            if let Some(sort) = aliases.get(name) {
                PureExpr::Var(name.clone(), Some(sort.clone()))
            } else {
                expr.clone()
            }
        }
        PureExpr::Deref(inner) => {
            if let PureExpr::Var(name, Some(ExprSort::Ref(_))) = inner.as_ref() {
                if let Some(sort) = aliases.get(name) {
                    return PureExpr::Var(name.clone(), Some(sort.clone()));
                }
            }
            PureExpr::Deref(std::sync::Arc::new(normalize_immutable_ref_deref_expr(
                inner, aliases,
            )))
        }
        PureExpr::BinOp(lhs, op, rhs) => PureExpr::BinOp(
            std::sync::Arc::new(normalize_immutable_ref_deref_expr(lhs, aliases)),
            *op,
            std::sync::Arc::new(normalize_immutable_ref_deref_expr(rhs, aliases)),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            std::sync::Arc::new(normalize_immutable_ref_deref_expr(inner, aliases)),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            std::sync::Arc::new(normalize_immutable_ref_deref_expr(cond, aliases)),
            std::sync::Arc::new(normalize_immutable_ref_deref_expr(then_expr, aliases)),
            std::sync::Arc::new(normalize_immutable_ref_deref_expr(else_expr, aliases)),
        ),
        PureExpr::Old(inner) => PureExpr::Old(std::sync::Arc::new(
            normalize_immutable_ref_deref_expr(inner, aliases),
        )),
        PureExpr::Final(inner) => PureExpr::Final(std::sync::Arc::new(
            normalize_immutable_ref_deref_expr(inner, aliases),
        )),
        PureExpr::View(inner) => PureExpr::View(std::sync::Arc::new(
            normalize_immutable_ref_deref_expr(inner, aliases),
        )),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: std::sync::Arc::new(normalize_immutable_ref_deref_expr(receiver, aliases)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| normalize_immutable_ref_deref_expr(arg, aliases))
                .collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: std::sync::Arc::new(normalize_immutable_ref_deref_expr(body, aliases)),
            triggers: triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|part| normalize_immutable_ref_deref_expr(part, aliases))
                        .collect()
                })
                .collect(),
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Exists {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: std::sync::Arc::new(normalize_immutable_ref_deref_expr(body, aliases)),
            triggers: triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|part| normalize_immutable_ref_deref_expr(part, aliases))
                        .collect()
                })
                .collect(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: std::sync::Arc::new(normalize_immutable_ref_deref_expr(scrutinee, aliases)),
            arms: arms
                .iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern.clone(),
                    body: normalize_immutable_ref_deref_expr(&arm.body, aliases),
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| normalize_immutable_ref_deref_expr(arg, aliases))
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: std::sync::Arc::new(normalize_immutable_ref_deref_expr(value, aliases)),
            body: std::sync::Arc::new(normalize_immutable_ref_deref_expr(body, aliases)),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: std::sync::Arc::new(normalize_immutable_ref_deref_expr(
                assumption, aliases,
            )),
            body: std::sync::Arc::new(normalize_immutable_ref_deref_expr(body, aliases)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: std::sync::Arc::new(normalize_immutable_ref_deref_expr(
                obligation, aliases,
            )),
            body: std::sync::Arc::new(normalize_immutable_ref_deref_expr(body, aliases)),
        },
        PureExpr::Closure { params, body } => PureExpr::Closure {
            params: params.clone(),
            body: std::sync::Arc::new(normalize_immutable_ref_deref_expr(body, aliases)),
        },
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {
            expr.clone()
        }
        #[allow(unreachable_patterns)]
        _ => expr.clone(),
    }
}

/// Extract a body result and its call effects up to an optional cutoff span.
///
/// Used by ghost semantic fact recovery (#2326) when callers need both the
/// returned expression tree (which may embed `LetAssume` call effects) and the
/// explicit `CallEffects` side channel from extraction.
pub(crate) fn extract_return_expr_with_cutoff_span<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    cutoff_span: Option<Span>,
) -> (Option<PureExpr>, CallEffects) {
    let config = ExtractionConfig {
        scope_call_context: true,
        cutoff_span,
        cutoff_location: None,
        diagnostics: None,
    };
    extract_return_expr_impl(
        tcx,
        body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        config,
    )
}

/// Extract source-name substitutions at a proof_assert program point.
///
/// The returned map rewrites source variables (for example `y`) to the
/// symbolic expressions known at `stop_span` (for example `call_1` or `x + 1`).
/// This lets proof_assert formulas talk about program-point state even though
/// the parser operates on source names.
pub(crate) fn extract_name_substitutions_until_span<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    stop_span: Span,
) -> Option<NameSubstitutions> {
    let cutoff = super::substitution::SubstitutionCutoff {
        stop_span: Some(stop_span),
        stop_location: None,
        region_span: None,
    };
    super::substitution::extract_substitutions_entry(
        tcx,
        body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        cutoff,
    )
}

/// Extract source-name substitutions up to `stop_span`, but only record
/// statement/call effects whose source spans are contained in `region_span`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn extract_name_substitutions_until_span_in_region<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    stop_span: Span,
    region_span: Span,
) -> Option<NameSubstitutions> {
    let cutoff = super::substitution::SubstitutionCutoff {
        stop_span: Some(stop_span),
        stop_location: None,
        region_span: Some(region_span),
    };
    super::substitution::extract_substitutions_entry(
        tcx,
        body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        cutoff,
    )
}

/// Extract source-name substitutions at a proof_assert MIR location.
pub(crate) fn extract_name_substitutions_until_location<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    stop_location: Location,
) -> Option<NameSubstitutions> {
    let cutoff = super::substitution::SubstitutionCutoff {
        stop_span: None,
        stop_location: Some(stop_location),
        region_span: None,
    };
    super::substitution::extract_substitutions_entry(
        tcx,
        body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        cutoff,
    )
}

/// Extract source-name substitutions at a proof_assert MIR location, limited
/// to statement/call effects whose source spans are contained in `region_span`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn extract_name_substitutions_until_location_in_region<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    stop_location: Location,
    region_span: Span,
) -> Option<NameSubstitutions> {
    let cutoff = super::substitution::SubstitutionCutoff {
        stop_span: None,
        stop_location: Some(stop_location),
        region_span: Some(region_span),
    };
    super::substitution::extract_substitutions_entry(
        tcx,
        body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        cutoff,
    )
}

/// Extract unified program-point state at a MIR location.
///
/// Performs both the return-expression extraction and the substitution
/// extraction for the same cutoff location in a single call. This replaces
/// the pattern where callers coordinated separate extraction passes.
///
/// Internally delegates to [`extract_return_expr_scoped_until_location_detailed`]
/// and [`extract_name_substitutions_until_location`]. (#2497)
pub(crate) fn extract_program_point_state_until_location_detailed<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    stop_location: Location,
) -> super::program_point_state::ScopedProgramPointState {
    let extraction_outcome = extract_return_expr_scoped_until_location_detailed(
        tcx,
        body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        stop_location,
    );
    let substitutions = extract_name_substitutions_until_location(
        tcx,
        body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        stop_location,
    )
    .unwrap_or_default();
    super::program_point_state::ScopedProgramPointState {
        return_expr: extraction_outcome.value,
        call_effects: extraction_outcome.effects,
        substitutions,
        diagnostics: extraction_outcome.diagnostics,
    }
}

/// Borrow the MIR while the caller retains its owned borrow-check handle.
pub(crate) fn get_mir_body<'a, 'tcx>(
    body_with_facts: &'a crate::callbacks::thread_locals::RetainedBorrowckBody<'tcx>,
) -> &'a Body<'tcx> {
    &body_with_facts.body
}
