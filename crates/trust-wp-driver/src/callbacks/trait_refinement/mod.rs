// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trait contract refinement verification.
//!
//! Verifies that an impl method's contract refines its trait method's contract:
//! - Pre-condition refinement: trait requires implies impl requires (contravariant)
//! - Post-condition refinement: impl ensures implies trait ensures (covariant)

mod prepare;
mod report;

#[cfg(test)]
mod tests;

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use trust_wp_ay::{verify_function_with_modes_outcome, VerificationRequest};
use trust_wp_core::{
    formula::{BinOp, PureExpr},
    logic::{LogicMode, TypeInvariantDef},
    TrackLevel,
};

use self::{
    prepare::prepare_refinement_clauses,
    report::{aggregate_refinement_counts, report_refinement_outcome_result},
};
use super::{
    super::contracts::{FunctionContract, TraitMethodContract},
    encoding_error_breakdown::EncodingErrorBreakdown,
    parsing::{conjoin_exprs, get_arg_names_from_def_id, parse_contract_clauses},
    reporting::VerificationCounters,
    verification_context::VerificationRunConfig,
};

/// Outcome counters from trait refinement verification.
#[allow(clippy::struct_field_names)]
pub(super) struct RefinementCounts {
    pub(super) verified_delta: i32,
    pub(super) assumed_delta: usize,
    pub(super) failed_delta: usize,
    pub(super) error_delta: usize,
    /// Demotion count from unsoundness demotion pipeline (#2106).
    /// Subset of `error_delta`.
    pub(super) demoted_delta: usize,
    /// Verified-shaped refinement results that lacked accepted proof evidence.
    pub(super) evidence_gap_delta: usize,
    /// Warnings emitted while classifying refinement results.
    pub(super) warning_delta: usize,
    /// Per-variant encoding-error breakdown for this refinement check (#2015).
    pub(super) encoding_errors: EncodingErrorBreakdown,
}

/// Parameters for trait contract refinement verification.
///
/// Bundles the impl method's transformed contract state with solver
/// configuration for the two-direction refinement check.
pub(super) struct TraitRefinementRequest<'a> {
    pub(super) impl_def_id: DefId,
    pub(super) impl_arg_names: &'a [String],
    pub(super) trait_contract: &'a TraitMethodContract,
    pub(super) base_requires: &'a [PureExpr],
    pub(super) base_ensures: &'a [PureExpr],
    pub(super) type_invariant_defs: &'a [TypeInvariantDef],
    pub(super) logic_fns_opt: Option<&'a [trust_wp_core::logic::LogicFnDef]>,
    pub(super) mode_overrides_opt: Option<&'a [LogicMode]>,
    pub(super) adt_decls: Option<&'a trust_wp_core::logic::AdtDecls>,
    pub(super) track_level: TrackLevel,
    pub(super) def_path: &'a str,
    pub(super) loc: &'a str,
    pub(super) verbose: bool,
}

/// Verify that an impl method's contract refines its trait method's contract.
///
/// Checks two directions:
/// 1. Pre-condition refinement: trait requires implies impl requires (contravariant)
/// 2. Post-condition refinement: impl ensures implies trait ensures (covariant)
pub(super) fn verify_trait_refinement(
    tcx: TyCtxt<'_>,
    req: &TraitRefinementRequest<'_>,
) -> RefinementCounts {
    let type_invariants_opt =
        (!req.type_invariant_defs.is_empty()).then_some(req.type_invariant_defs);
    let prepared = match prepare_refinement_clauses(tcx, req) {
        Ok(prepared) => prepared,
        Err(error) => {
            eprintln!("trust-wp: {} trait refinement error: {error}", req.def_path);
            return refinement_error_counts();
        }
    };

    let pre_refinement = verify_function_with_modes_outcome(
        VerificationRequest::new(&prepared.trait_requires, &prepared.impl_requires)
            .logic_fns(req.logic_fns_opt)
            .mode_overrides(req.mode_overrides_opt)
            .type_invariants(type_invariants_opt)
            .adt_decls(req.adt_decls.cloned())
            .track(Some(req.track_level)),
    );

    let post_refinement_obligations =
        build_post_refinement_obligations(&prepared.impl_ensures, &prepared.trait_ensures);
    let post_refinement = verify_function_with_modes_outcome(
        VerificationRequest::new(&prepared.trait_requires, &post_refinement_obligations)
            .return_expr(prepared.result_expr.as_ref())
            .logic_fns(req.logic_fns_opt)
            .mode_overrides(req.mode_overrides_opt)
            .type_invariants(type_invariants_opt)
            .adt_decls(req.adt_decls.cloned())
            .track(Some(req.track_level)),
    );

    // Record encoding-error subtypes before consuming the results (#2015).
    let mut encoding_errors = EncodingErrorBreakdown::default();
    if let Err(ref error) = pre_refinement {
        encoding_errors.record(error);
    }
    if let Err(ref error) = post_refinement {
        encoding_errors.record(error);
    }

    let pre_outcome = report_refinement_outcome_result(
        pre_refinement,
        req.def_path,
        &prepared.trait_method_path,
        "trait precondition implies impl precondition",
        req.loc,
    );
    let post_outcome = report_refinement_outcome_result(
        post_refinement,
        req.def_path,
        &prepared.trait_method_path,
        "impl postcondition implies trait postcondition",
        req.loc,
    );

    aggregate_refinement_counts(
        pre_outcome,
        post_outcome,
        req.verbose,
        req.def_path,
        encoding_errors,
    )
}

fn build_post_refinement_obligations(
    impl_ensures: &[PureExpr],
    trait_ensures: &[PureExpr],
) -> Vec<PureExpr> {
    let impl_post = conjoin_exprs(impl_ensures);
    trait_ensures
        .iter()
        .cloned()
        .map(|trait_post| {
            if impl_ensures
                .iter()
                .any(|impl_post| impl_post == &trait_post)
            {
                PureExpr::Bool(true)
            } else {
                PureExpr::BinOp(
                    Arc::new(impl_post.clone()),
                    BinOp::Implies,
                    Arc::new(trait_post),
                )
            }
        })
        .collect()
}

fn refinement_error_counts() -> RefinementCounts {
    RefinementCounts {
        verified_delta: -1,
        assumed_delta: 0,
        failed_delta: 0,
        error_delta: 1,
        demoted_delta: 0,
        evidence_gap_delta: 0,
        warning_delta: 0,
        encoding_errors: EncodingErrorBreakdown::default(),
    }
}

/// Check trait refinement for a logic function that was skipped from body verification.
///
/// Logic functions are axiomatized (body not verified), but when a logic function
/// is a trait impl that overrides trait contracts, the refinement obligation still
/// applies: the impl's precondition must be weaker (contravariant) and the impl's
/// postcondition must be stronger (covariant) than the trait's. (#2686)
pub(super) fn check_logic_fn_trait_refinement(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    config: &VerificationRunConfig<'_>,
    trait_contract_map: &HashMap<DefId, HashMap<String, &TraitMethodContract>>,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
    unverified_axioms: &HashSet<String>,
    counters: &mut VerificationCounters,
) {
    let def_path = tcx.def_path_str(contract.def_id);
    let has_explicit_contracts = !contract.requires.is_empty() || !contract.ensures.is_empty();

    // Concrete law postconditions are intentionally exposed as axioms in
    // default compat mode. Do not reintroduce eager law proof through the
    // impl-vs-trait refinement side path; strict-axioms keeps the proof check.
    if !config.strict_axioms
        && logic_fns.iter().any(|logic_fn| {
            logic_fn.is_law()
                && (logic_fn.full_path() == def_path
                    || logic_fn.full_path().ends_with(&format!("::{def_path}")))
        })
    {
        return;
    }

    // Check if this logic function is already in the unverified axioms set.
    // When the postcondition was already marked as unverifiable (e.g., body
    // contains parameterized closures, #985, #2676), trait refinement failures
    // should be warnings rather than hard failures — the function is already
    // tracked as an unverified axiom. (#2665)
    //
    // `def_path` from `tcx.def_path_str` omits the crate name, while
    // `unverified_axioms` entries may include it (e.g., "creusot_test::Foo::bar"
    // vs "Foo::bar"). Match by suffix to handle both.
    let is_already_unverified = unverified_axioms
        .iter()
        .any(|a| a == &def_path || a.ends_with(&format!("::{def_path}")));

    // Only check contracts that are in the refinement overrides set.
    if !config.trait_refinement_overrides.contains(&contract.def_id) {
        // Soundness diagnostic (#2663): warn when a logic function has explicit
        // contracts AND a trait origin but was not included in the refinement
        // overrides set. This indicates a gap in find_trait_refinement_overrides.
        if has_explicit_contracts && contract.trait_origin.is_some() {
            eprintln!(
                "trust-wp: WARNING: {def_path} logic-fn has explicit contracts and trait origin \
                 but is NOT in trait_refinement_overrides — refinement check silently skipped (#2663)"
            );
            // When the body has parameterized closures, the postcondition is
            // already unverifiable — downgrade to warning instead of failure
            // to avoid penalizing WellFounded-style trait impls. (#2665)
            if is_already_unverified {
                counters.warnings += 1;
            } else {
                // Count as a failed refinement to prevent false accepts.
                counters.failed += 1;
            }
        }
        return;
    }
    let Some(origin) = contract.trait_origin.as_ref() else {
        // Soundness diagnostic (#2663): should not reach here if the contract
        // was in the refinement overrides set (which requires trait_origin).
        if has_explicit_contracts {
            eprintln!(
                "trust-wp: WARNING: {def_path} logic-fn in refinement overrides but has no \
                 trait_origin — refinement check silently skipped (#2663)"
            );
        }
        return;
    };
    let Some(trait_contract) = trait_contract_map.get(&origin.trait_def_id).and_then(
        |methods: &HashMap<String, &TraitMethodContract>| methods.get(&origin.trait_method_name),
    ) else {
        // The trait method has no explicit contracts (#2676). Check whether the
        // method actually exists in the trait — if so, the absence from
        // trait_contract_map simply means the trait method has no
        // #[requires]/#[ensures], and the refinement is trivially satisfied
        // (the impl is free to add any contract).
        let trait_method_exists = tcx
            .associated_items(origin.trait_def_id)
            .in_definition_order()
            .any(|item| {
                tcx.def_kind(item.def_id) == rustc_hir::def::DefKind::AssocFn
                    && item.name().as_str() == origin.trait_method_name
            });

        if trait_method_exists {
            // Trait method exists but has no contracts — refinement is trivially
            // satisfied. The impl can strengthen postconditions and weaken
            // preconditions freely when the trait imposes no constraints.
            return;
        }

        // Soundness diagnostic (#2663): the impl overrides trait contracts but
        // the trait method was not found at all. This indicates a genuine
        // discovery gap (e.g., the trait is external or the method was renamed).
        eprintln!(
            "trust-wp: WARNING: {def_path} logic-fn trait refinement: trait contract for \
             {}::{} not found in trait_contract_map — refinement check silently skipped (#2663)",
            tcx.def_path_str(origin.trait_def_id),
            origin.trait_method_name,
        );
        // When the body has parameterized closures, the postcondition is
        // already unverifiable — downgrade to warning instead of failure
        // to avoid penalizing WellFounded-style trait impls. (#2665)
        if is_already_unverified {
            counters.warnings += 1;
        } else {
            // Count as a failed refinement to prevent false accepts.
            counters.failed += 1;
        }
        return;
    };

    let loc = format!("{:?}", tcx.def_span(contract.def_id));

    // Parse the impl's requires/ensures clauses.
    let base_requires = match parse_contract_clauses(&contract.requires, "requires", &def_path) {
        Ok(exprs) => exprs,
        Err(e) => {
            eprintln!(
                "trust-wp: {def_path} logic-fn refinement error: failed to parse requires: {e}"
            );
            counters.errors += 1;
            return;
        }
    };
    let base_ensures = match parse_contract_clauses(&contract.ensures, "ensures", &def_path) {
        Ok(exprs) => exprs,
        Err(e) => {
            eprintln!(
                "trust-wp: {def_path} logic-fn refinement error: failed to parse ensures: {e}"
            );
            counters.errors += 1;
            return;
        }
    };

    // Get argument names for the impl method.
    let arg_names = get_arg_names_from_def_id(tcx, contract.def_id).unwrap_or_default();

    let logic_fns_opt = (!logic_fns.is_empty()).then_some(logic_fns);

    let refinement_req = TraitRefinementRequest {
        impl_def_id: contract.def_id,
        impl_arg_names: &arg_names,
        trait_contract,
        base_requires: &base_requires,
        base_ensures: &base_ensures,
        type_invariant_defs: config.type_invariant_defs,
        logic_fns_opt,
        mode_overrides_opt: None,
        adt_decls: None,
        track_level: config.track_level,
        def_path: &def_path,
        loc: &loc,
        verbose: config.verbose,
    };
    let counts = verify_trait_refinement(tcx, &refinement_req);

    // Apply refinement results to counters.
    // For logic functions, the function itself isn't counted as verified,
    // but refinement failures still need to be reported.
    if counts.failed_delta > 0 {
        counters.failed += counts.failed_delta;
    }
    if counts.error_delta > 0 {
        counters.errors += counts.error_delta;
    }
    counters.demoted += counts.demoted_delta;
    counters.evidence_gaps += counts.evidence_gap_delta;
    counters.warnings += counts.warning_delta;
    counters.encoding_errors.merge_from(&counts.encoding_errors);
}
