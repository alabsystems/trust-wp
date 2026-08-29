// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

use rustc_hir::def_id::DefId;
use rustc_middle::{mir::BasicBlock, ty::TyCtxt};
use tracing::info_span;
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::{tuple_field_logic_fn_index, tuple_field_logic_fn_name},
        ProjectedFinalPin, PureExpr,
    },
    tracing_init::{TIMING_STAGE_EXTRACT_SPAN, TIMING_STAGE_PARSE_SPAN},
};
use trust_wp_driver::StdSpec;

use super::{
    arg_names::{
        closure_capture_substitutions, collapse_projected_field_captures,
        collect_mut_ref_arg_names, get_arg_names_for_mir_extraction,
    },
    clauses::{parse_clause_inputs, ParsedClauseInputs},
    types::{LoopFields, LoopObligationGroup, MutBorrowFields, ParsedContract},
};
use crate::{
    callbacks::{discovery::is_bodyful_trait_method, try_get_body_with_context},
    contracts::FunctionContract,
    mir_analysis::{
        clear_qualified_assoc_const_definitions, collect_call_effects_for_blocks,
        collect_loop_body_call_obligations, detect_loops, diagnostics::ExtractionDiagnostics,
        extract_loop_body, extract_mut_borrow_body, extract_param_destructuring_substitutions,
        extract_return_expr_spanned, extract_return_expr_with_context_detailed, get_mir_body,
        normalize_immutable_ref_param_derefs, take_qualified_assoc_const_definitions,
        CallSpecContext, LoopAnalysis, LoopBodySpecContext, MutBorrowBody, SpannedBodyExpr,
    },
};

#[derive(Default)]
struct ExtractionData {
    result_expr: Option<PureExpr>,
    result_expr_spanned: Option<SpannedBodyExpr>,
    mut_borrow_body: Option<MutBorrowBody>,
    /// Caller-side expiry pins proven by `projected_expiry` (#prophecy-slots M5).
    projected_final_pins: Vec<ProjectedFinalPin>,
    loop_analysis: Option<LoopAnalysis>,
    loop_obligation_groups: Vec<LoopObligationGroup>,
    mut_ref_param_names: HashSet<String>,
    param_destructuring_subs: HashMap<String, PureExpr>,
    call_assumptions: Vec<PureExpr>,
    pre_loop_call_assumptions: Vec<PureExpr>,
    call_obligations: Vec<PureExpr>,
    pre_loop_call_obligations: Vec<PureExpr>,
    post_loop_call_obligations: Vec<PureExpr>,
}

pub(in crate::callbacks) struct ExtractionContext<'a> {
    pub(super) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) extern_specs: &'a HashMap<String, StdSpec>,
    pub(super) report_errors: bool,
    pub(super) has_type_invariant_injection: bool,
}

impl<'a> ExtractionContext<'a> {
    pub(in crate::callbacks) fn new(
        user_specs: &'a HashMap<DefId, StdSpec>,
        trait_specs: &'a HashMap<DefId, StdSpec>,
        extern_specs: &'a HashMap<String, StdSpec>,
        report_errors: bool,
        has_type_invariant_injection: bool,
    ) -> Self {
        Self {
            user_specs,
            trait_specs,
            extern_specs,
            report_errors,
            has_type_invariant_injection,
        }
    }
}

/// Parse a contract's expressions and extract MIR body.
/// Returns None if there are no valid contract expressions.
pub(in crate::callbacks) fn parse_and_extract_contract(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    recursive_fns: &HashSet<DefId>,
    ctx: &ExtractionContext<'_>,
) -> Option<ParsedContract> {
    let parse_span = info_span!(TIMING_STAGE_PARSE_SPAN).entered();
    let mut clause_inputs = parse_clause_inputs(tcx, contract, ctx.report_errors)?;

    apply_capture_substitutions(tcx, contract, &mut clause_inputs);
    clause_inputs.rewrite_each_expr(|expr| {
        crate::assoc_const_paths::normalize_local_assoc_const_paths(tcx, contract.def_id, expr)
    });

    let has_explicit_or_injected_clauses =
        clause_inputs.has_explicit_clauses() || ctx.has_type_invariant_injection;

    // Most empty-contract functions are intentionally skipped.
    // Exception: trait default methods with bodies may still carry call-site
    // obligations that must be proved (e.g., default method calls contracted
    // trait method, #1203).
    let allow_body_only_obligation_check = is_bodyful_trait_method(tcx, contract.local_def_id);
    if !has_explicit_or_injected_clauses && !allow_body_only_obligation_check {
        return None;
    }

    drop(parse_span);

    let extract_span = info_span!(TIMING_STAGE_EXTRACT_SPAN).entered();
    let arg_names = prepare_arg_names(tcx, contract, &clause_inputs.ensures)?;
    warm_mir_cache(tcx, contract);

    clear_qualified_assoc_const_definitions();
    let mut extraction_data = extract_contract_body(
        tcx,
        contract,
        recursive_fns,
        &arg_names,
        clause_inputs.needs_loop_analysis(),
        ctx,
    );

    let mut assoc_const_substitutions = take_qualified_assoc_const_definitions();
    assoc_const_substitutions
        .extend(crate::mir_analysis::extract::collect_generic_assoc_const_definitions(tcx));
    clause_inputs.rewrite_all_exprs(&assoc_const_substitutions);
    clause_inputs.rewrite_all_exprs(&extraction_data.param_destructuring_subs);
    if let Some(body_with_context) = try_get_body_with_context(contract.local_def_id) {
        let mir_body = get_mir_body(body_with_context);
        let normalize_ref_derefs = normalize_immutable_ref_param_derefs(tcx, mir_body, &arg_names);
        clause_inputs.rewrite_each_expr(|expr| normalize_ref_derefs(expr));
    }
    apply_capture_substitutions_to_extraction_data(tcx, contract, &mut extraction_data);
    drop(extract_span);

    let mut parsed = assemble_parsed_contract(contract, clause_inputs, arg_names, extraction_data);
    // Recognize the recursive `&mut self` match-reborrow shape (rusthorn
    // take_some) for prophecy-pinning premise synthesis in per_contract.
    if let Some(body_with_context) = try_get_body_with_context(contract.local_def_id) {
        let mir_body = get_mir_body(body_with_context);
        parsed.reborrow_prophecy = crate::mir_analysis::analyze_reborrow_prophecy(
            tcx,
            contract.def_id,
            mir_body,
            &parsed.arg_names,
        );
    }
    rewrite_current_closure_projected_fields(tcx, contract, &mut parsed);
    Some(parsed)
}

fn apply_capture_substitutions(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    clause_inputs: &mut ParsedClauseInputs,
) {
    // For closures, map captured variable names to closure-env field names so
    // contracts and MIR extraction use the same symbols (Phase 3, #358).
    let result = closure_capture_substitutions(tcx, contract.local_def_id);
    clause_inputs.rewrite_all_exprs(&result.substitutions);

    // Rust 2021 minimal captures: when a closure captures `p.1` (not the whole
    // `p`), collapse `__trust_wp_tuple_get_1(Var("p"))` → `Var("self.N")`. (#2554)
    if !result.projected_captures.is_empty() {
        clause_inputs.rewrite_each_expr(|expr| {
            collapse_projected_field_captures(expr, &result.projected_captures)
        });
    }
}

#[allow(clippy::needless_pass_by_value)] // PureExpr by-value is idiomatic for rewrite chains
fn rewrite_closure_capture_expr(
    expr: PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    projected_captures: &[(String, usize, String)],
) -> PureExpr {
    let substituted = expr.substitute(substitutions);
    if projected_captures.is_empty() {
        substituted
    } else {
        collapse_projected_field_captures(&substituted, projected_captures)
    }
}

fn apply_capture_substitutions_to_extraction_data(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    extraction_data: &mut ExtractionData,
) {
    let result = closure_capture_substitutions(tcx, contract.local_def_id);
    if result.substitutions.is_empty() && result.projected_captures.is_empty() {
        return;
    }

    let rewrite = |expr: PureExpr| {
        rewrite_closure_capture_expr(expr, &result.substitutions, &result.projected_captures)
    };

    extraction_data.result_expr = extraction_data.result_expr.take().map(&rewrite);
    extraction_data.result_expr_spanned =
        extraction_data
            .result_expr_spanned
            .take()
            .map(|spanned| SpannedBodyExpr {
                expr: rewrite(spanned.expr),
                span: spanned.span,
            });
    extraction_data.call_assumptions = extraction_data
        .call_assumptions
        .drain(..)
        .map(&rewrite)
        .collect();
    extraction_data.pre_loop_call_assumptions = extraction_data
        .pre_loop_call_assumptions
        .drain(..)
        .map(&rewrite)
        .collect();
    extraction_data.call_obligations = extraction_data
        .call_obligations
        .drain(..)
        .map(&rewrite)
        .collect();
    extraction_data.pre_loop_call_obligations = extraction_data
        .pre_loop_call_obligations
        .drain(..)
        .map(&rewrite)
        .collect();
    extraction_data.post_loop_call_obligations = extraction_data
        .post_loop_call_obligations
        .drain(..)
        .map(&rewrite)
        .collect();
    for group in &mut extraction_data.loop_obligation_groups {
        group.condition = group.condition.clone().map(&rewrite);
        group.obligations = group.obligations.drain(..).map(&rewrite).collect();
    }
}

fn rewrite_current_closure_projected_fields(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    parsed: &mut ParsedContract,
) {
    if tcx.def_kind(contract.local_def_id.to_def_id()) != rustc_hir::def::DefKind::Closure {
        return;
    }

    parsed.rewrite_all_exprs(rewrite_current_closure_projected_field_expr);
}

fn rewrite_current_closure_projected_field_expr(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(rewrite_current_closure_projected_field_node)
}

fn rewrite_current_closure_projected_field_node(expr: PureExpr) -> PureExpr {
    if let Some(projected) = rewrite_current_closure_nested_tuple_selector(&expr) {
        return projected;
    }
    let PureExpr::Var(name, _) = &expr else {
        return expr;
    };
    let mut segments = name.split('.');
    let Some("self") = segments.next() else {
        return expr;
    };
    let Some(capture_idx) = segments.next() else {
        return expr;
    };
    if capture_idx.parse::<usize>().is_err() {
        return expr;
    }

    let field_path: Option<Vec<usize>> = segments
        .map(|segment| segment.parse::<usize>().ok())
        .collect();
    let Some(field_path) = field_path else {
        return expr;
    };
    if field_path.is_empty() {
        return expr;
    }

    let mut projected = PureExpr::Var(format!("self.{capture_idx}"), None);
    for field_idx in field_path {
        projected = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(field_idx),
            args: vec![projected],
        };
    }
    projected
}

fn rewrite_current_closure_nested_tuple_selector(expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    if args.len() != 1 || tuple_field_logic_fn_index(name).is_none() {
        return None;
    }
    let PureExpr::LogicFnCall {
        name: capture_selector,
        args: capture_args,
    } = &args[0]
    else {
        return None;
    };
    let capture_idx = tuple_field_logic_fn_index(capture_selector)?;
    if !matches!(
        capture_args.as_slice(),
        [PureExpr::Var(base, _)] if base == "self"
    ) {
        return None;
    }
    Some(PureExpr::LogicFnCall {
        name: name.clone(),
        args: vec![PureExpr::Var(format!("self.{capture_idx}"), None)],
    })
}

fn prepare_arg_names(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    ensures: &[PureExpr],
) -> Option<Vec<String>> {
    let arg_names = get_arg_names_for_mir_extraction(tcx, contract.def_id, contract.local_def_id);

    // Reject functions where a parameter is named `result` and ensures clauses
    // use it as a free variable. The `result` identifier is reserved for the
    // return value in postconditions; a parameter with the same name creates an
    // ambiguity that can cause unsound verification (#674).
    //
    // Closure-binder forms like `#[ensures(|(fst, snd)| fst == snd)]` are safe
    // because the closure parameters shadow the reserved name — `"result"` is
    // not free in the parsed postcondition (#2304).
    if arg_names.iter().any(|name| name == "result") && ensures_uses_reserved_result_name(ensures) {
        let def_path = tcx.def_path_str(contract.def_id);
        eprintln!(
            "trust-wp: error: function `{def_path}` has a parameter named `result`, \
             which conflicts with the reserved `result` identifier in #[ensures] postconditions"
        );
        return None;
    }

    Some(arg_names)
}

/// Returns `true` if any `ensures` clause uses `"result"` as a free variable.
///
/// Closure parameters, quantifier binders, let bindings, and match patterns
/// all shadow the name, so `#[ensures(|(fst, snd)| fst == snd)]` returns
/// `false` even when the function has a parameter named `result` (#2304).
pub(super) fn ensures_uses_reserved_result_name(ensures: &[PureExpr]) -> bool {
    ensures
        .iter()
        .any(|expr| expr.free_vars().contains("result"))
}

fn warm_mir_cache(tcx: TyCtxt<'_>, contract: &FunctionContract) {
    // Trigger borrow checking to populate MIR_BODIES cache (#414)
    // Without this, try_get_body_with_context returns None and we can't
    // extract mut_borrow_body for mutable reference verification.
    // Guard: skip items without an HIR body. Required trait methods are the
    // key case: `is_mir_available` can still be true because rustc synthesizes
    // an unreachable shim, but `mir_borrowck` panics via `body_owned_by`.
    // (#972, #2437)
    let def_id = contract.local_def_id.to_def_id();
    if !tcx.is_mir_available(def_id)
        || tcx
            .hir_node_by_def_id(contract.local_def_id)
            .body_id()
            .is_none()
    {
        return;
    }

    let root = tcx.typeck_root_def_id(def_id).expect_local();
    let _ = tcx.mir_borrowck(root);
}

pub(super) fn effective_user_specs_for_extraction<'a>(
    contract: &FunctionContract,
    recursive_fns: &HashSet<DefId>,
    arg_names: &[String],
    user_specs: &'a HashMap<DefId, StdSpec>,
) -> Cow<'a, HashMap<DefId, StdSpec>> {
    if recursive_fns.contains(&contract.def_id)
        && (!contract.requires.is_empty() || !contract.ensures.is_empty())
    {
        let self_spec = StdSpec {
            requires: contract.requires.clone(),
            ensures: contract.ensures.clone(),
            param_names: Some(arg_names.to_vec()),
        };
        let mut merged = user_specs.clone();
        merged.insert(contract.def_id, self_spec);
        Cow::Owned(merged)
    } else {
        Cow::Borrowed(user_specs)
    }
}

fn extract_contract_body(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    recursive_fns: &HashSet<DefId>,
    arg_names: &[String],
    needs_loop_analysis: bool,
    ctx: &ExtractionContext<'_>,
) -> ExtractionData {
    let Some(body_with_facts) = try_get_body_with_context(contract.local_def_id) else {
        return ExtractionData::default();
    };

    // Self-spec injection: ensure the function's own spec includes explicit
    // param_names so that recursive self-calls resolve via DirectSpec with
    // correct parameter-to-argument substitutions. build_user_spec_table
    // inserts specs with param_names: None; adding explicit param_names here
    // ensures resolve_arg_names_or_warn has a fallback for recursive calls
    // where tcx arg name resolution might fail (#1322).
    let effective_user_specs =
        effective_user_specs_for_extraction(contract, recursive_fns, arg_names, ctx.user_specs);

    let mir_body = get_mir_body(body_with_facts);
    // Try to extract return expression with context for function call support
    // This uses TyCtxt to resolve function paths and look up std specs
    let context_outcome = extract_return_expr_with_context_detailed(
        tcx,
        mir_body,
        arg_names,
        &effective_user_specs,
        ctx.trait_specs,
        ctx.extern_specs,
    );
    // Also extract with source spans for better error reporting
    // Now supports function calls with std spec lookup (see #63)
    let result_expr_spanned = extract_return_expr_spanned(
        tcx,
        mir_body,
        arg_names,
        &effective_user_specs,
        ctx.trait_specs,
        ctx.extern_specs,
    );
    let used_spanned_fallback = context_outcome.value.is_none() && result_expr_spanned.is_some();
    if ctx.report_errors && context_outcome.value.is_none() {
        if let Some(warning) = format_context_extraction_warning(
            &tcx.def_path_str(contract.def_id),
            &context_outcome.diagnostics,
            used_spanned_fallback,
        ) {
            eprintln!("{warning}");
        }
    }
    let extraction_effects = context_outcome.effects;
    // Fallback: when context extraction returns None but the spanned pass
    // succeeds, reuse the spanned expression as the body result so
    // postconditions involving `result` are still connected to the return value.
    let result_expr = context_outcome
        .value
        .or_else(|| result_expr_spanned.as_ref().map(|sp| sp.expr.clone()));

    // #prophecy-slots M5: prove the caller-side death points for `&mut`
    // borrows that arrive inside a call result. Independent of the `&mut`
    // parameter lane: a body with no `&mut` parameters can still take a
    // payload borrow out of a call and let it expire.
    let projected_expiry =
        crate::mir_analysis::projected_expiry::collect_projected_expiry_pins(
            tcx, mir_body, arg_names,
        );
    if !projected_expiry.is_empty() {
        tracing::debug!(
            "projected_expiry: {} PROVEN caller-side expiry pin(s) in {}",
            projected_expiry.pins.len(),
            tcx.def_path_str(contract.def_id),
        );
    }
    if !projected_expiry.disarms.is_empty() {
        tracing::debug!(
            "projected_expiry: {} candidate shape(s) disarmed in {}: {:?}",
            projected_expiry.disarms.len(),
            tcx.def_path_str(contract.def_id),
            projected_expiry.disarms,
        );
    }
    let projected_final_pins = projected_expiry.pins;

    // Try to extract mutable borrow body (for &mut parameters)
    let mut_borrow_body = extract_mut_borrow_body(
        tcx,
        mir_body,
        Some(body_with_facts),
        arg_names,
        &effective_user_specs,
        ctx.trait_specs,
        ctx.extern_specs,
    );
    let delayed_writeback_assumptions = mut_borrow_body.as_ref().map_or_else(Vec::new, |body| {
        // Parents whose final value was spec-advanced to a non-identity
        // post-state (e.g. `v.push(x)`: `^v == push_back(*v, ..)`) get the
        // same `*parent == ^child` suppression as mutation-continued
        // parents: the delayed (two-phase) writeback would fuse the
        // entry-time `parent_current` with the post-mutation child final
        // and collapse base premises to UNSAT (bug/two_phase).
        let mut suppressed_parents = body.mutation_continued_params.clone();
        for (name, final_expr) in &body.final_values {
            if !is_identity_final_value_expr(name, final_expr) {
                suppressed_parents.insert(name.clone());
            }
        }
        filter_delayed_writebacks_for_mutation_continued(
            &body.delayed_writeback_assumptions,
            &suppressed_parents,
        )
    });

    // Detect loops if there are invariants or variants to verify
    let loop_analysis = needs_loop_analysis.then(|| detect_loops(mir_body));

    // Collect per-loop call-site obligations paired with their loop
    // conditions (#752). The function-level extraction walks INTO loop
    // bodies (default on_false_edge continues through FalseUnwind), so
    // calls inside loops DO trigger apply_preconditions and appear in
    // extraction_effects.obligations. Walk each loop's body blocks
    // separately and pair obligations with the loop's condition.
    //
    // For nested loops, each loop's obligations use *exclusive* body blocks
    // (excluding inner loop non-header blocks). Without this, calls inside
    // an inner loop get collected for the outer loop's obligation group with
    // the outer loop's condition, causing false verification failures when
    // the inner loop's condition is needed to prove the precondition.
    let loop_condition_spec_ctx = CallSpecContext {
        tcx,
        user_specs: &effective_user_specs,
        trait_specs: ctx.trait_specs,
        extern_specs: ctx.extern_specs,
    };

    let loop_obligation_groups: Vec<LoopObligationGroup> = loop_analysis
        .as_ref()
        .map(|analysis| {
            analysis
                .loops
                .iter()
                .map(|loop_info| {
                    // Compute exclusive body blocks: remove blocks belonging to
                    // inner loops (keeping their headers for CFG traversal).
                    let exclusive_blocks = {
                        let mut blocks = loop_info.body_blocks.clone();
                        for other in &analysis.loops {
                            if other.header != loop_info.header
                                && loop_info.body_blocks.contains(&other.header)
                            {
                                for bb in &other.body_blocks {
                                    if *bb != other.header {
                                        blocks.remove(bb);
                                    }
                                }
                            }
                        }
                        blocks
                    };
                    let name_restore_blocks = {
                        let mut blocks = loop_info.body_blocks.clone();
                        for other in &analysis.loops {
                            if other.header != loop_info.header
                                && other.body_blocks.contains(&loop_info.header)
                            {
                                blocks.extend(other.body_blocks.iter().copied());
                            }
                        }
                        blocks
                    };
                    let loop_spec_ctx = LoopBodySpecContext {
                        user_specs: &effective_user_specs,
                        trait_specs: ctx.trait_specs,
                        extern_specs: ctx.extern_specs,
                        body_blocks: &exclusive_blocks,
                        name_restore_blocks: Some(&name_restore_blocks),
                    };
                    let obligations = collect_loop_body_call_obligations(
                        tcx,
                        mir_body,
                        arg_names,
                        loop_info.header,
                        &loop_spec_ctx,
                    );
                    let pre_loop_bbs = collect_pre_loop_blocks(mir_body, &loop_info.body_blocks);
                    let assumptions = if pre_loop_bbs.is_empty() {
                        Vec::new()
                    } else {
                        collect_call_effects_for_blocks(
                            tcx,
                            mir_body,
                            arg_names,
                            &pre_loop_bbs,
                            &effective_user_specs,
                            ctx.trait_specs,
                            ctx.extern_specs,
                        )
                        .assumptions
                        .into_iter()
                        .filter(expr_mentions_call_result_var)
                        .collect()
                    };
                    let condition = extract_loop_body(
                        mir_body,
                        arg_names,
                        loop_info,
                        Some(&analysis.loops),
                        Some(&loop_condition_spec_ctx),
                        false,
                    )
                    .condition;
                    LoopObligationGroup {
                        assumptions,
                        obligations,
                        condition,
                    }
                })
                .collect()
        })
        .unwrap_or_default();

    // Extract name substitutions for destructured parameters (#1075).
    // When parameters use tuple/struct destructuring, the HIR name
    // extraction falls back to positional names. The debug info in MIR
    // provides the actual binding names used in contracts.
    let param_destructuring_subs =
        extract_param_destructuring_substitutions(tcx, mir_body, arg_names);

    // Filter both call_assumptions AND call_obligations to exclude in-loop
    // effects when loop analysis is active. (#2496)
    //
    // The function-level MIR extraction walks into loop bodies and collects
    // call effects from ALL BBs — including those inside loops. For obligations,
    // the per-loop obligation groups separately collect these with proper loop
    // conditions. For assumptions, the leak is more dangerous: loop-body
    // postcondition-derived assumptions (e.g., `seen == true`) become
    // unconditional facts on the post-loop VC, even though the loop may execute
    // zero times.
    //
    // Fix: gate on loop presence (not obligation non-empty), because a loop can
    // contribute assumptions without contributing any precondition obligations.
    // Use block-scoped extraction on the non-loop BB complement to recover only
    // the pre/post-loop call effects.
    let (
        call_assumptions,
        pre_loop_call_assumptions,
        call_obligations,
        pre_loop_call_obligations,
        post_loop_call_obligations,
    ) = if loop_analysis
        .as_ref()
        .is_some_and(|analysis| analysis.has_loops)
    {
        // Compute all loop body BBs across all loops.
        let all_loop_bbs: HashSet<rustc_middle::mir::BasicBlock> = loop_analysis
            .as_ref()
            .map(|a| {
                a.loops
                    .iter()
                    .flat_map(|l| l.body_blocks.iter().copied())
                    .collect()
            })
            .unwrap_or_default();
        // Build the complement: all function BBs minus loop body BBs.
        let non_loop_bbs: HashSet<_> = mir_body
            .basic_blocks
            .indices()
            .filter(|bb| !all_loop_bbs.contains(bb))
            .collect();
        let pre_loop_bbs = collect_pre_loop_blocks(mir_body, &all_loop_bbs);
        let post_loop_bbs: HashSet<_> = non_loop_bbs
            .iter()
            .copied()
            .filter(|bb| !pre_loop_bbs.contains(bb))
            .collect();
        if non_loop_bbs.is_empty() {
            (
                delayed_writeback_assumptions,
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            )
        } else {
            let non_loop_effects = collect_call_effects_for_blocks(
                tcx,
                mir_body,
                arg_names,
                &non_loop_bbs,
                &effective_user_specs,
                ctx.trait_specs,
                ctx.extern_specs,
            );
            let (pre_loop_assumptions, pre_loop_obligations) = if pre_loop_bbs.is_empty() {
                (Vec::new(), Vec::new())
            } else {
                let effects = collect_call_effects_for_blocks(
                    tcx,
                    mir_body,
                    arg_names,
                    &pre_loop_bbs,
                    &effective_user_specs,
                    ctx.trait_specs,
                    ctx.extern_specs,
                );
                (effects.assumptions, effects.obligations)
            };
            let post_loop_obligations = if post_loop_bbs.is_empty() {
                Vec::new()
            } else {
                collect_call_effects_for_blocks(
                    tcx,
                    mir_body,
                    arg_names,
                    &post_loop_bbs,
                    &effective_user_specs,
                    ctx.trait_specs,
                    ctx.extern_specs,
                )
                .obligations
            };
            // Mapping closure axioms are universally quantified and sound
            // regardless of loop execution. Include them from the full
            // extraction to avoid losing axioms that the block-scoped
            // walker cannot detect (requires full extraction context).
            let mut assumptions = non_loop_effects.assumptions;
            let normalize_ref_derefs =
                normalize_immutable_ref_param_derefs(tcx, mir_body, arg_names);
            for assumption in &mut assumptions {
                *assumption = normalize_ref_derefs(assumption);
            }
            for mc in &extraction_effects.mapping_closures {
                if let Some(axiom) = mc.to_forall_axiom() {
                    assumptions.push(axiom);
                }
            }
            // map_inv per-element ensures + length axioms are universally
            // quantified and sound regardless of loop execution. (#2170)
            for mi in &extraction_effects.map_inv_closures {
                assumptions.extend(mi.to_view_axioms());
            }
            assumptions.extend(delayed_writeback_assumptions);
            (
                assumptions,
                pre_loop_assumptions,
                non_loop_effects.obligations,
                pre_loop_obligations,
                post_loop_obligations,
            )
        }
    } else {
        // No loops: use the full extraction effects directly.
        let mut assumptions = extraction_effects.assumptions;
        let normalize_ref_derefs = normalize_immutable_ref_param_derefs(tcx, mir_body, arg_names);
        for assumption in &mut assumptions {
            *assumption = normalize_ref_derefs(assumption);
        }
        for mc in &extraction_effects.mapping_closures {
            if let Some(axiom) = mc.to_forall_axiom() {
                assumptions.push(axiom);
            }
        }
        // map_inv per-element ensures + length axioms (#2170).
        for mi in &extraction_effects.map_inv_closures {
            assumptions.extend(mi.to_view_axioms());
        }
        assumptions.extend(delayed_writeback_assumptions);
        let obligations = extraction_effects.obligations;
        (
            assumptions.clone(),
            assumptions,
            obligations.clone(),
            obligations,
            Vec::new(),
        )
    };

    ExtractionData {
        result_expr,
        result_expr_spanned,
        mut_borrow_body,
        projected_final_pins,
        loop_analysis,
        loop_obligation_groups,
        mut_ref_param_names: collect_mut_ref_arg_names(tcx, mir_body, arg_names),
        param_destructuring_subs,
        call_assumptions,
        pre_loop_call_assumptions,
        call_obligations,
        pre_loop_call_obligations,
        post_loop_call_obligations,
    }
}

fn collect_pre_loop_blocks(
    body: &rustc_middle::mir::Body<'_>,
    all_loop_bbs: &HashSet<BasicBlock>,
) -> HashSet<BasicBlock> {
    let mut visited = HashSet::new();
    let mut worklist = vec![BasicBlock::from_u32(0)];
    while let Some(bb) = worklist.pop() {
        if all_loop_bbs.contains(&bb) || !visited.insert(bb) {
            continue;
        }
        for succ in body.basic_blocks[bb].terminator().successors() {
            if !all_loop_bbs.contains(&succ) {
                worklist.push(succ);
            }
        }
    }
    visited
}

fn expr_mentions_call_result_var(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => name.starts_with("call_"),
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_mentions_call_result_var(lhs) || expr_mentions_call_result_var(rhs)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_mentions_call_result_var(inner),
        PureExpr::Let { value, body, .. } => {
            expr_mentions_call_result_var(value) || expr_mentions_call_result_var(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            expr_mentions_call_result_var(assumption) || expr_mentions_call_result_var(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            expr_mentions_call_result_var(obligation) || expr_mentions_call_result_var(body)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_mentions_call_result_var(cond)
                || expr_mentions_call_result_var(then_expr)
                || expr_mentions_call_result_var(else_expr)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            expr_mentions_call_result_var(body)
                || triggers.iter().flatten().any(expr_mentions_call_result_var)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(expr_mentions_call_result_var),
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_mentions_call_result_var(receiver)
                || args.iter().any(expr_mentions_call_result_var)
        }
        PureExpr::Closure { body, .. } => expr_mentions_call_result_var(body),
        _ => false,
    }
}

pub(super) fn format_context_extraction_warning(
    def_path: &str,
    diagnostics: &ExtractionDiagnostics,
    used_spanned_fallback: bool,
) -> Option<String> {
    let detail = diagnostics.render_summary()?;
    let status = if used_spanned_fallback {
        "using spanned fallback after context extraction failed"
    } else {
        "MIR context extraction failed"
    };
    Some(format!("trust-wp: warning: {def_path}: {status}: {detail}"))
}

fn assemble_parsed_contract(
    contract: &FunctionContract,
    clause_inputs: ParsedClauseInputs,
    arg_names: Vec<String>,
    extraction_data: ExtractionData,
) -> ParsedContract {
    let ParsedClauseInputs {
        requires,
        ensures,
        invariants,
        per_loop_invariants,
        per_loop_variants,
        variants,
    } = clause_inputs;

    let ExtractionData {
        result_expr,
        result_expr_spanned,
        mut_borrow_body,
        projected_final_pins,
        loop_analysis,
        loop_obligation_groups,
        mut_ref_param_names,
        param_destructuring_subs: _,
        call_assumptions,
        pre_loop_call_assumptions,
        call_obligations,
        pre_loop_call_obligations,
        post_loop_call_obligations,
    } = extraction_data;

    ParsedContract {
        requires,
        ensures,
        result_expr,
        result_expr_spanned,
        arg_names,
        call_assumptions,
        pre_loop_call_assumptions,
        call_obligations,
        pre_loop_call_obligations,
        post_loop_call_obligations,
        loop_fields: LoopFields {
            invariants,
            per_loop_invariants,
            per_loop_variants,
            all_loop_spans: contract.all_loop_spans.clone(),
            variants,
            loop_analysis,
            loop_obligation_groups,
        },
        mut_borrow: MutBorrowFields {
            mut_borrow_body,
            mut_ref_param_names,
            projected_final_pins,
        },
        reborrow_prophecy: None,
    }
}

/// Filter delayed-writeback assumptions for mutation-continued parents
/// (bug/682 / #5).
///
/// `build_delayed_writeback_assumptions` (trust-wp-driver `mir_analysis`)
/// emits two flavors of equality per two-phase writeback:
///   1. `*parent == ^child`  (the reservation-time writeback)
///   2. `^parent == ^child`  (the final-side propagation, only when `child`
///      is final at the reborrow site)
///
/// When the parent is in `mutation_continued_params`, the call_assumption
/// already advances `parent_final` through the child's final on the *post-
/// call* side. The encoder uses a single SSA-style `<parent>_current` name
/// for the parent's *entry-time* current value, so asserting
/// `*parent == ^child` (= `parent_current == child_final`) fuses the
/// entry-time current with the post-call value. Combined with a
/// precondition that pins `*parent` to a concrete value (e.g.
/// `*a == 3u64` in bug/682) and the call_assumption
/// (`child_final > parent_current`), this collapses base premises to UNSAT
/// and trips the vacuity guard. This is the delayed-writeback (two-phase
/// borrow) analogue of the gate in
/// `crates/trust-wp-ay/src/verify/mut_borrow/resolve.rs::emit_prophecy_writebacks`
/// (the existing #2663 / Phase 3 fix only catches the *immediate* writeback
/// path).
///
/// The `^parent == ^child` propagation is the prophecy chain on the *final*
/// side and is consistent with the call_assumption, so it is preserved.
/// Identity-final check mirroring
/// `trust-wp-ay::verify::mut_borrow::resolve::is_identity_final_value`:
/// `Deref(Var(name))` (possibly through branch-symmetric `Ite`s) means the
/// parameter's exit state is its entry state — everything else is an advanced
/// (post-mutation) final value.
fn is_identity_final_value_expr(var_name: &str, final_expr: &PureExpr) -> bool {
    match final_expr {
        PureExpr::Deref(inner) => {
            matches!(inner.as_ref(), PureExpr::Var(name, _) if name == var_name)
        }
        PureExpr::Ite(_, then_branch, else_branch) => {
            is_identity_final_value_expr(var_name, then_branch)
                && is_identity_final_value_expr(var_name, else_branch)
        }
        _ => false,
    }
}

fn filter_delayed_writebacks_for_mutation_continued(
    assumptions: &[PureExpr],
    mutation_continued_params: &HashSet<String>,
) -> Vec<PureExpr> {
    if mutation_continued_params.is_empty() {
        return assumptions.to_vec();
    }
    assumptions
        .iter()
        .filter(|expr| {
            !is_deref_var_eq_final_var_for_mutation_continued(expr, mutation_continued_params)
        })
        .cloned()
        .collect()
}

/// Match `Deref(Var(name, _)) == Final(Var(_, _))` where `name` is a
/// mutation-continued parameter. Returns `true` when the assumption is the
/// `*parent == ^child` reservation-time writeback that must be suppressed.
fn is_deref_var_eq_final_var_for_mutation_continued(
    expr: &PureExpr,
    mutation_continued_params: &HashSet<String>,
) -> bool {
    let PureExpr::BinOp(lhs, trust_wp_core::formula::BinOp::Eq, rhs) = expr else {
        return false;
    };
    let parent_name = extract_deref_var_name(lhs);
    let is_final_var = matches!(rhs.as_ref(), PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(_, _)));
    if !is_final_var {
        return false;
    }
    parent_name.is_some_and(|name| mutation_continued_params.contains(&name))
}

fn extract_deref_var_name(expr: &PureExpr) -> Option<String> {
    if let PureExpr::Deref(inner) = expr {
        if let PureExpr::Var(name, _) = inner.as_ref() {
            return Some(name.clone());
        }
    }
    None
}

#[cfg(test)]
mod delayed_writeback_filter_tests {
    use std::sync::Arc;

    use trust_wp_core::formula::BinOp;

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn reservation_writeback(parent: &str, child: &str) -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(var(parent)))),
            BinOp::Eq,
            Arc::new(PureExpr::Final(Arc::new(var(child)))),
        )
    }

    fn final_writeback(parent: &str, child: &str) -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(var(parent)))),
            BinOp::Eq,
            Arc::new(PureExpr::Final(Arc::new(var(child)))),
        )
    }

    #[test]
    fn advanced_parent_suppresses_only_its_reservation_writeback() {
        let suppressed = HashSet::from(["v".to_string()]);
        let v_reservation = reservation_writeback("v", "v_child");
        let v_final = final_writeback("v", "v_child");
        let other_reservation = reservation_writeback("other", "other_child");
        let assumptions = vec![
            v_reservation.clone(),
            v_final.clone(),
            other_reservation.clone(),
        ];

        let filtered = filter_delayed_writebacks_for_mutation_continued(&assumptions, &suppressed);

        assert!(!filtered.contains(&v_reservation));
        assert!(filtered.contains(&v_final));
        assert!(filtered.contains(&other_reservation));
    }

    #[test]
    fn identity_final_detection_requires_every_branch_to_preserve_entry_value() {
        let identity = PureExpr::Deref(Arc::new(var("v")));
        let advanced = PureExpr::Final(Arc::new(var("v_child")));
        let condition = Arc::new(PureExpr::Bool(true));

        assert!(is_identity_final_value_expr("v", &identity));
        assert!(is_identity_final_value_expr(
            "v",
            &PureExpr::Ite(
                condition.clone(),
                Arc::new(identity.clone()),
                Arc::new(identity.clone()),
            )
        ));
        assert!(!is_identity_final_value_expr(
            "v",
            &PureExpr::Ite(
                condition.clone(),
                Arc::new(advanced.clone()),
                Arc::new(advanced.clone()),
            ),
        ));
        assert!(!is_identity_final_value_expr(
            "v",
            &PureExpr::Ite(condition, Arc::new(identity), Arc::new(advanced)),
        ));
    }
}
