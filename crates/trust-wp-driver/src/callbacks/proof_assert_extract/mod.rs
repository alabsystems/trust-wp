// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof assertion extraction and simplification helpers.

mod projected_writes;
mod simplification;
mod substitutions;
mod view_normalization;

use std::{collections::HashMap, sync::Arc};

// Re-export public API so all existing `proof_assert_extract::foo` imports work.
pub(super) use projected_writes::{
    apply_projected_writes_to_substitutions, is_projected_write_repair_assumption,
};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    Node, TraitFn, TraitItemKind,
};
use rustc_middle::{mir::Location, ty::TyCtxt};
use rustc_span::Span;
pub(super) use simplification::{
    apply_constructor_equality_substitutions, apply_constructor_equality_substitutions_to_facts,
    apply_type_and_field_rewrites, constructor_equality_to_tester_selector_facts,
    normalize_old_constructor_equality_facts, reduce_concrete_constructor_method_calls,
    reduce_concrete_matches, simplify_proof_assert_expr, synthesize_constructor_equalities,
    synthesize_ground_equality_substitution_facts,
};
#[cfg(test)]
pub(super) use substitutions::resolve_internal_references;
pub(super) use substitutions::{
    is_deref_precondition, resolve_internal_references_at_current_state, substitution_assumptions,
    without_current_pointee_keys,
};
use tracing::debug;
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};
use trust_wp_driver::StdSpec;
pub(super) use view_normalization::{
    collapse_idempotent_views, normalize_scalar_proof_assert_boundary,
    normalize_seq_final_fact_views, normalize_view_fn_calls,
};
pub(crate) use view_normalization::{
    is_provably_view_identity_domain, preserve_transparent_adapter_view_witness,
    transparent_adapter_inner,
};

use super::{
    ghost_context::{
        closure_capture_names, derive_final_deref_ghost_substitutions,
        extract_ghost_closure_effects, extract_ghost_closure_substitutions,
        find_ghost_closure_def_ids_in_mir, rewrite_closure_substitution_capture_names,
        rewrite_ghost_closure_capture_vars,
    },
    parsing::get_arg_names_from_def_id,
    try_get_body_with_context,
    verification_context::ProofAssertContext,
};
use crate::{
    ghost::GhostBlock,
    mir_analysis::{
        diagnostics::ExtractionDiagnostics, extract_name_substitutions_until_location_in_region,
        extract_program_point_state_until_location_detailed, extract_return_expr_with_cutoff_span,
        get_mir_body, NameSubstitutions,
    },
};

/// Strip `LetAssume`/`LetObligation` from expression tree, returning
/// (stripped_body, assumptions, obligations). (#746, #815)
pub(super) fn extract_call_effects(
    return_expr: Option<&PureExpr>,
) -> (Option<PureExpr>, Vec<PureExpr>, Vec<PureExpr>) {
    let Some(expr) = return_expr else {
        return (None, Vec::new(), Vec::new());
    };
    let mut assumptions = Vec::new();
    let mut obligations = Vec::new();
    let stripped = strip_call_effects(expr, &mut assumptions, &mut obligations);
    (Some(stripped), assumptions, obligations)
}

/// Per-assertion parameters for proof_assert body extraction (#2657).
///
/// Bundles the assertion-specific location and context data that varies
/// per proof_assert, keeping `extract_body_for_proof_assert` under clippy's
/// `too_many_arguments` threshold.
pub(super) struct ProofAssertExtractionParams<'a> {
    pub(super) containing_fn: LocalDefId,
    pub(super) proof_assert_span: Span,
    pub(super) proof_assert_location: Location,
    pub(super) proof_assert_ghost_block: Option<&'a GhostBlock>,
}

/// Extract MIR body result for a proof_assert's containing function.
/// Stops at the assertion location.
///
/// Returns `(return_expr, local_substitutions, phase1_call_assumptions,
/// phase1_call_obligations, has_mutating_call_effect, mapping_closures)`:
/// - `return_expr`: The PureExpr tree with `LetAssume`/`LetObligation` for projected writes.
/// - `local_substitutions`: Name→expression map for program-point variable state.
/// - `phase1_call_assumptions`: Predicate-style postconditions (e.g., FSet/FMap spec
///   effects like `fset_contains(set_final, 1)`) accumulated during body extraction.
///   These are NOT embedded in the return_expr tree (only projected_write_facts are);
///   the caller must add them as preconditions. (#1581)
/// - `phase1_call_obligations`: Matching precondition obligations for side-channel
///   phase-1 call assumptions. These must be proved with the proof_assert to
///   avoid assuming callee postconditions without discharging their requires.
/// - `mapping_closures`: Closure body info from `Mapping::from_closure` calls.
///   Used for direct ground instantiation in proof_assert verification. (#2245)
#[allow(clippy::type_complexity)]
pub(super) fn extract_body_for_proof_assert(
    tcx: TyCtxt<'_>,
    params: &ProofAssertExtractionParams<'_>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
    fn_path: &str,
) -> (
    Option<PureExpr>,
    NameSubstitutions,
    Vec<PureExpr>,
    Vec<PureExpr>,
    bool,
    Vec<crate::mir_analysis::effects::MappingClosureInfo>,
) {
    let containing_fn = params.containing_fn;
    let proof_assert_span = params.proof_assert_span;
    let proof_assert_location = params.proof_assert_location;
    let proof_assert_ghost_block = params.proof_assert_ghost_block;
    let trait_specs = ctx.trait_specs;
    let verbose = ctx.verbose;

    // Ensure borrow checking has run within the active MIR-retention scope.
    if tcx.is_mir_available(containing_fn.to_def_id()) {
        // Skip bodyless trait method declarations (#2205). `is_mir_available`
        // returns true for these but `mir_borrowck` panics in `body_owned_by`.
        if let Node::TraitItem(item) = tcx.hir_node_by_def_id(containing_fn) {
            if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
                return (
                    None,
                    NameSubstitutions::default(),
                    Vec::new(),
                    Vec::new(),
                    false,
                    Vec::new(),
                );
            }
        }
        let root = tcx
            .typeck_root_def_id(containing_fn.to_def_id())
            .expect_local();
        let _ = tcx.mir_borrowck(root);
    }

    let Some(body_with_facts) = try_get_body_with_context(tcx, containing_fn) else {
        return (
            None,
            NameSubstitutions::default(),
            Vec::new(),
            Vec::new(),
            false,
            Vec::new(),
        );
    };
    let mir_body = get_mir_body(&body_with_facts);

    // Extract unified program-point state: return expression, call effects,
    // and substitutions in a single coordinated pass. (#2497)
    let program_point_state = extract_program_point_state_until_location_detailed(
        tcx,
        mir_body,
        arg_names,
        user_specs,
        trait_specs,
        ctx.extern_specs,
        proof_assert_location,
    );
    // Collect call-site postcondition assumptions AND Mapping::from_closure
    // forall axioms. The function-level path (extraction.rs:406) injects these;
    // the proof_assert path was missing them, causing such_that witnesses to be
    // opaque. Ground instantiation happens in proof_assert_verify.rs where
    // call_assumptions (from LetAssume) are also available. (#2245, #2316)
    let mut phase1_assumptions = program_point_state.call_effects.assumptions.clone();
    let mut phase1_obligations = Vec::new();
    for mc in &program_point_state.call_effects.mapping_closures {
        if let Some(axiom) = mc.to_forall_axiom() {
            phase1_assumptions.push(axiom);
        }
    }
    let (_, span_effects) = extract_return_expr_with_cutoff_span(
        tcx,
        mir_body,
        arg_names,
        user_specs,
        trait_specs,
        ctx.extern_specs,
        Some(proof_assert_span),
    );
    for assumption in &span_effects.assumptions {
        if !phase1_assumptions.contains(assumption) {
            phase1_assumptions.push(assumption.clone());
        }
    }
    for mc in &span_effects.mapping_closures {
        if !program_point_state
            .call_effects
            .mapping_closures
            .iter()
            .any(|existing| existing.result_var == mc.result_var)
        {
            if let Some(axiom) = mc.to_forall_axiom() {
                phase1_assumptions.push(axiom);
            }
        }
    }
    // A ghost block's own walk and its closures' effects read a parameter's
    // name as its value at the block; the main walk's values read it as the
    // entry value, which the lane names apart from the current one for a
    // parameter whose name means nothing else in them (D-241). Read in the
    // main walk's terms, the ghost values join the map that renaming then
    // treats as one.
    let entry_terms_of_current = ghost_entry_terms_of_current(
        tcx,
        mir_body,
        arg_names,
        proof_assert_location,
        proof_assert_ghost_block.is_some(),
        &program_point_state.substitutions,
    );
    let in_entry_terms = |expr: PureExpr| -> PureExpr {
        if entry_terms_of_current.is_empty() {
            expr
        } else {
            expr.substitute(&entry_terms_of_current)
        }
    };
    if let Some(ghost_block) = proof_assert_ghost_block {
        for closure_def_id in find_ghost_closure_def_ids_in_mir(mir_body, ghost_block.span) {
            let capture_names = closure_capture_names(tcx, closure_def_id);
            let closure_effects = extract_ghost_closure_effects(
                tcx,
                closure_def_id,
                Some(proof_assert_span),
                user_specs,
                trait_specs,
                ctx.extern_specs,
            );
            for fact in closure_effects.assumptions {
                let fact =
                    in_entry_terms(rewrite_ghost_closure_capture_vars(&fact, &capture_names));
                if !phase1_assumptions.contains(&fact) {
                    phase1_assumptions.push(fact);
                }
            }
            for obligation in closure_effects.obligations {
                let obligation = in_entry_terms(rewrite_ghost_closure_capture_vars(
                    &obligation,
                    &capture_names,
                ));
                if !phase1_obligations.contains(&obligation) {
                    phase1_obligations.push(obligation);
                }
            }
        }
    }

    let mut substitutions = program_point_state.substitutions;
    if let Some(ghost_block) = proof_assert_ghost_block {
        let mir_ctx = ProofAssertMirContext {
            tcx,
            mir_body,
            arg_names,
            user_specs,
            trait_specs,
            extern_specs: ctx.extern_specs,
        };
        augment_proof_assert_ghost_block_substitutions(
            &mir_ctx,
            proof_assert_span,
            proof_assert_location,
            ghost_block,
            &in_entry_terms,
            &mut substitutions,
        );
    }
    if verbose {
        if program_point_state.return_expr.is_some() {
            debug!("trust-wp:   (proof_assert in {fn_path}: MIR body extracted)");
        } else {
            debug!(
                "{}",
                format_proof_assert_extraction_message(fn_path, &program_point_state.diagnostics)
            );
        }
    }
    let has_mutating_call_effect = program_point_state.call_effects.has_mutating_call_effect
        || span_effects.has_mutating_call_effect;
    let mapping_closures = program_point_state.call_effects.mapping_closures;
    (
        program_point_state.return_expr,
        substitutions,
        phase1_assumptions,
        phase1_obligations,
        has_mutating_call_effect,
        mapping_closures,
    )
}

/// Per-proof-assert MIR extraction context (#2657).
///
/// Bundles the MIR body, argument names, and spec maps that are constant
/// across a single `extract_body_for_proof_assert` call, keeping
/// `augment_proof_assert_ghost_block_substitutions` under clippy's
/// argument threshold.
struct ProofAssertMirContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    mir_body: &'a rustc_middle::mir::Body<'tcx>,
    arg_names: &'a [String],
    user_specs: &'a HashMap<DefId, StdSpec>,
    trait_specs: &'a HashMap<DefId, StdSpec>,
    extern_specs: &'a HashMap<String, StdSpec>,
}

fn augment_proof_assert_ghost_block_substitutions(
    mir_ctx: &ProofAssertMirContext<'_, '_>,
    proof_assert_span: Span,
    proof_assert_location: Location,
    ghost_block: &GhostBlock,
    in_entry_terms: &dyn Fn(PureExpr) -> PureExpr,
    substitutions: &mut NameSubstitutions,
) {
    if let Some(mut ghost_block_substitutions) = extract_name_substitutions_until_location_in_region(
        mir_ctx.tcx,
        mir_ctx.mir_body,
        mir_ctx.arg_names,
        mir_ctx.user_specs,
        mir_ctx.trait_specs,
        mir_ctx.extern_specs,
        proof_assert_location,
        ghost_block.span,
    ) {
        derive_final_deref_ghost_substitutions(&mut ghost_block_substitutions);
        for value in ghost_block_substitutions.values_mut() {
            *value = in_entry_terms(value.clone());
        }
        substitutions.extend(ghost_block_substitutions);
    }

    for closure_def_id in find_ghost_closure_def_ids_in_mir(mir_ctx.mir_body, ghost_block.span) {
        if let Some(mut closure_substitutions) = extract_ghost_closure_substitutions(
            mir_ctx.tcx,
            closure_def_id,
            Some(proof_assert_span),
            Some(ghost_block.span),
            mir_ctx.user_specs,
            mir_ctx.trait_specs,
            mir_ctx.extern_specs,
        ) {
            let capture_names = closure_capture_names(mir_ctx.tcx, closure_def_id);
            rewrite_closure_substitution_capture_names(&mut closure_substitutions, &capture_names);
            derive_final_deref_ghost_substitutions(&mut closure_substitutions);
            for value in closure_substitutions.values_mut() {
                *value = in_entry_terms(value.clone());
            }
            substitutions.extend(closure_substitutions);
        }
    }
}

/// For an assertion in a ghost block, each parameter the `proof_assert` lane
/// may name apart from its entry value
/// ([`crate::mir_analysis::params_with_renamable_entry`]) mapped to its
/// binding at the assertion in the main walk (D-241). A ghost block cannot
/// write a program parameter, so the parameter's value at the block is that
/// binding, whose own name is the entry value. Empty outside a ghost block
/// and in a closure, whose lane names no entry value apart.
fn ghost_entry_terms_of_current<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &rustc_middle::mir::Body<'tcx>,
    arg_names: &[String],
    at: Location,
    in_ghost_block: bool,
    main_substitutions: &NameSubstitutions,
) -> HashMap<String, PureExpr> {
    if !in_ghost_block || tcx.is_closure_like(mir_body.source.def_id()) {
        return HashMap::new();
    }
    crate::mir_analysis::params_with_renamable_entry(tcx, mir_body, at)
        .into_keys()
        .filter_map(|local| {
            let name = arg_names.get(local.as_usize().checked_sub(1)?)?;
            let binding = main_substitutions.get(name)?;
            Some((name.clone(), binding.clone()))
        })
        .collect()
}

pub(super) fn format_proof_assert_extraction_message(
    fn_path: &str,
    diagnostics: &ExtractionDiagnostics,
) -> String {
    if let Some(detail) = diagnostics.render_summary() {
        return format!(
            "trust-wp:   (proof_assert in {fn_path}: MIR body extraction failed: {detail}; using preconditions only)"
        );
    }
    format!("trust-wp:   (proof_assert in {fn_path}: MIR body extraction failed, using preconditions only)")
}

/// Build argument names for proof_assert MIR body extraction.
///
/// Closure MIR includes an implicit environment argument (`_1`) that is absent
/// from HIR parameter lists. Use `self` for this slot to match the extraction
/// conventions used by contract verification.
pub(super) fn get_arg_names_for_proof_assert_body(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
) -> Vec<String> {
    let def_id = local_def_id.to_def_id();
    let mut names = get_arg_names_from_def_id(tcx, def_id).unwrap_or_else(|| {
        let path = tcx.def_path_str(def_id);
        debug!(
            "trust-wp: warning: no parameter names for `{path}` ({def_id:?}), \
             using positional fallback — named contract parameters will not be substituted"
        );
        Vec::new()
    });
    if tcx.def_kind(local_def_id.to_def_id()) == DefKind::Closure {
        names.insert(0, "self".to_string());
    }
    names
}

/// Recursively strip LetAssume/LetObligation from an expression tree,
/// collecting assumptions and obligations into the output vectors.
///
/// For effects inside `Ite` branches, collected expressions are guarded with
/// their path conditions (`path ==> effect`) so branch-local assumptions and
/// obligations remain properly scoped.
pub(super) fn strip_call_effects(
    expr: &PureExpr,
    assumptions: &mut Vec<PureExpr>,
    obligations: &mut Vec<PureExpr>,
) -> PureExpr {
    strip_call_effects_with_path(expr, None, assumptions, obligations)
}

fn strip_call_effects_with_path(
    expr: &PureExpr,
    path_cond: Option<&PureExpr>,
    assumptions: &mut Vec<PureExpr>,
    obligations: &mut Vec<PureExpr>,
) -> PureExpr {
    match expr {
        PureExpr::LetAssume { assumption, body } => {
            assumptions.push(guard_with_path(assumption, path_cond));
            strip_call_effects_with_path(body, path_cond, assumptions, obligations)
        }
        PureExpr::LetObligation { obligation, body } => {
            obligations.push(guard_with_path(obligation, path_cond));
            strip_call_effects_with_path(body, path_cond, assumptions, obligations)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let then_path = path_with(path_cond, cond);
            let else_guard = PureExpr::UnOp(UnOp::Not, Arc::new((**cond).clone()));
            let else_path = path_with(path_cond, &else_guard);
            let then_stripped =
                strip_call_effects_with_path(then_expr, Some(&then_path), assumptions, obligations);
            let else_stripped =
                strip_call_effects_with_path(else_expr, Some(&else_path), assumptions, obligations);
            PureExpr::Ite(
                cond.clone(),
                Arc::new(then_stripped),
                Arc::new(else_stripped),
            )
        }
        // For non-LetAssume/LetObligation nodes, return as-is.
        // The marker expression (Int(0) or _0) passes through unchanged.
        other => other.clone(),
    }
}

fn path_with(path_cond: Option<&PureExpr>, branch_cond: &PureExpr) -> PureExpr {
    match path_cond {
        Some(path) => PureExpr::BinOp(
            Arc::new(path.clone()),
            BinOp::And,
            Arc::new(branch_cond.clone()),
        ),
        None => branch_cond.clone(),
    }
}

fn guard_with_path(effect: &PureExpr, path_cond: Option<&PureExpr>) -> PureExpr {
    match path_cond {
        Some(path) => PureExpr::BinOp(
            Arc::new(path.clone()),
            BinOp::Implies,
            Arc::new(effect.clone()),
        ),
        None => effect.clone(),
    }
}
