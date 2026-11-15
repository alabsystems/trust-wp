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
mod scope;

pub(crate) use prepare::std_prelude_glob_module;

#[cfg(test)]
mod tests;

use std::{
    collections::HashMap,
    panic::{catch_unwind, AssertUnwindSafe},
    sync::Arc,
    time::Duration,
};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use trust_wp_ay::{verify_function_with_modes_outcome, VerificationRequest};
use trust_wp_core::{
    formula::{BinOp, PureExpr},
    logic::{LogicMode, TypeInvariantDef},
    TrackLevel,
};
use trust_wp_driver::{lookup_spec_with_extern, StdSpec};

use self::{
    prepare::prepare_refinement_clauses,
    report::{aggregate_refinement_counts, report_refinement_outcome_result, RefinementOutcome},
};
use super::{
    super::contracts::{FunctionContract, TraitMethodContract},
    adt_analysis::build_adt_decls,
    encoding_error_breakdown::EncodingErrorBreakdown,
    helpers::scope_logic_fn_modes,
    parsing::{conjoin_exprs, get_arg_names_from_def_id, parse_contract_clauses},
    reporting::VerificationCounters,
    verification_context::VerificationRunConfig,
};

/// Outcome counters from trait refinement verification.
#[allow(clippy::struct_field_names)]
pub(super) struct RefinementCounts {
    /// `-1` when the refinement is not established. Refinement runs in its
    /// own pass and no longer demotes the body verdict, so only tests read it.
    #[cfg_attr(not(test), allow(dead_code))]
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
    /// The impl's clause text `base_requires` / `base_ensures` were parsed
    /// from, read again for the types the AST does not carry.
    pub(super) impl_requires_text: &'a [String],
    pub(super) impl_ensures_text: &'a [String],
    pub(super) type_invariant_defs: &'a [TypeInvariantDef],
    pub(super) logic_fns_opt: Option<&'a [trust_wp_core::logic::LogicFnDef]>,
    pub(super) mode_overrides_opt: Option<&'a [LogicMode]>,
    pub(super) adt_decls: Option<&'a trust_wp_core::logic::AdtDecls>,
    pub(super) track_level: TrackLevel,
    pub(super) def_path: &'a str,
    pub(super) loc: &'a str,
    pub(super) verbose: bool,
    /// Check only `trait requires => impl requires` and never credit a
    /// `refinement verified` verdict. Used for external traits, whose
    /// trust-wp specs are call-site facts (e.g. `T::clone.postcondition`),
    /// not the trait-level contract Creusot's refinement goal is stated over.
    pub(super) precondition_only: bool,
    /// Both sides' clauses are the trait method's, renamed position by
    /// position to the impl's parameter names, and the impl's body owes them
    /// restated in the trait's own resolution (`restate_inherited_clauses`).
    /// Equal text then IS equal meaning, so preparation does not refuse a
    /// clause for naming something scope-dependent, and the clauses are
    /// premises of the refinement, never its goals; the goals derived from
    /// types (argument and result invariants) are still checked.
    pub(super) clauses_are_the_trait_s: bool,
    /// The driver's solver budget, the same one every function-contract
    /// request carries. A refinement goal is a verification request like any
    /// other: without it the request runs in the short-budget regime, where
    /// the literal-`false` witness lane is skipped and a refuted refinement
    /// (`impl requires(false)` under a trait with no requires) can only be
    /// withheld, never published as `FAILED` with its model.
    pub(super) timeout: Option<Duration>,
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

    // A direction with no remaining obligation is a literal tautology (every
    // goal is `true` or a clause the premise side states verbatim, compared
    // after parameter normalization and sort annotation); no solver call is
    // made and nothing is assumed. Any other obligation goes to the solver.
    // The verbatim comparison is sound only because preparation refused
    // every clause naming something scope-dependent and every clause whose
    // text writes a type the AST does not record (casts, ascriptions, `let`
    // annotations, binders not of type `Int`/`bool`): the remaining terms
    // mean the same thing on both sides, and equal ASTs are equal including
    // every written type. An inherited contract skips that refusal because
    // its user clauses are one text on both sides, and they are premises
    // only: a goal there is derived from types.
    let pre_refinement_obligations = build_pre_refinement_obligations(
        &prepared.trait_requires,
        &prepared.impl_requires[prepared.premise_only_impl_requires..],
    );
    let pre_refinement = if pre_refinement_obligations.is_empty() {
        None
    } else {
        Some(verify_function_with_modes_outcome(
            VerificationRequest::new(&prepared.trait_requires, &pre_refinement_obligations)
                .logic_fns(req.logic_fns_opt)
                .mode_overrides(req.mode_overrides_opt)
                .type_invariants(type_invariants_opt)
                .adt_decls(req.adt_decls.cloned())
                .track(Some(req.track_level))
                .timeout(req.timeout),
        ))
    };

    let post_refinement_obligations = build_post_refinement_obligations(
        &prepared.impl_ensures,
        &prepared.trait_ensures[prepared.premise_only_trait_ensures..],
    );
    let post_refinement = if req.precondition_only || post_refinement_obligations.is_empty() {
        None
    } else {
        Some(verify_function_with_modes_outcome(
            VerificationRequest::new(&prepared.trait_requires, &post_refinement_obligations)
                .return_expr(prepared.result_expr.as_ref())
                .logic_fns(req.logic_fns_opt)
                .mode_overrides(req.mode_overrides_opt)
                .type_invariants(type_invariants_opt)
                .adt_decls(req.adt_decls.cloned())
                .track(Some(req.track_level))
                .timeout(req.timeout),
        ))
    };

    // Record encoding-error subtypes before consuming the results (#2015).
    let mut encoding_errors = EncodingErrorBreakdown::default();
    if let Some(Err(ref error)) = pre_refinement {
        encoding_errors.record(error);
    }
    if let Some(Err(ref error)) = post_refinement {
        encoding_errors.record(error);
    }

    let pre_outcome = pre_refinement.map_or(RefinementOutcome::Verified, |result| {
        report_refinement_outcome_result(
            result,
            req.def_path,
            &prepared.trait_method_path,
            "trait precondition implies impl precondition",
            req.loc,
        )
    });
    let post_outcome = post_refinement.map_or(RefinementOutcome::Verified, |result| {
        report_refinement_outcome_result(
            result,
            req.def_path,
            &prepared.trait_method_path,
            "impl postcondition implies trait postcondition",
            req.loc,
        )
    });

    aggregate_refinement_counts(
        pre_outcome,
        post_outcome,
        req.precondition_only,
        req.def_path,
        encoding_errors,
    )
}

/// Pre-condition refinement goals: every impl `requires` clause that the trait
/// side does not state verbatim. `true` clauses are dropped.
fn build_pre_refinement_obligations(
    trait_requires: &[PureExpr],
    impl_requires: &[PureExpr],
) -> Vec<PureExpr> {
    impl_requires
        .iter()
        .filter(|impl_pre| {
            !matches!(impl_pre, PureExpr::Bool(true))
                && !trait_requires
                    .iter()
                    .any(|trait_pre| trait_pre == *impl_pre)
        })
        .cloned()
        .collect()
}

/// Post-condition refinement goals: `impl_ensures => trait_post` for every
/// trait `ensures` clause the impl does not state verbatim. `true` trait
/// clauses are dropped, so an empty trait postcondition yields no goal.
fn build_post_refinement_obligations(
    impl_ensures: &[PureExpr],
    trait_ensures: &[PureExpr],
) -> Vec<PureExpr> {
    let impl_post = conjoin_exprs(impl_ensures);
    trait_ensures
        .iter()
        .filter(|trait_post| {
            !matches!(trait_post, PureExpr::Bool(true))
                && !impl_ensures
                    .iter()
                    .any(|impl_post| impl_post == *trait_post)
        })
        .cloned()
        .map(|trait_post| {
            PureExpr::BinOp(
                Arc::new(impl_post.clone()),
                BinOp::Implies,
                Arc::new(trait_post),
            )
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

/// Where the trait-side contract of a refinement check comes from.
pub(super) enum TraitSideContract<'a> {
    /// Contract declared on a local trait method.
    Declared(&'a TraitMethodContract),
    /// A local trait method without a contract: `requires` is `true` and there
    /// is no `ensures` (call sites through the trait resolve to the same
    /// empty contract).
    LocalEmpty(TraitMethodContract),
    /// An external trait method, with the trust-wp spec call sites through
    /// the trait resolve to, when there is one.
    External {
        trait_method_path: String,
        spec: Option<TraitMethodContract>,
    },
}

/// Resolve the effective trait-side contract for a trait impl method.
///
/// Returns `None` only when the contract has no trait origin or rustc cannot
/// name the trait method it implements.
pub(super) fn resolve_trait_side_contract<'a>(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    trait_contract_map: &'a HashMap<DefId, HashMap<String, &'a TraitMethodContract>>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Option<TraitSideContract<'a>> {
    let origin = contract.trait_origin.as_ref()?;
    if let Some(trait_contract) = trait_contract_map
        .get(&origin.trait_def_id)
        .and_then(|methods| methods.get(&origin.trait_method_name))
    {
        return Some(TraitSideContract::Declared(trait_contract));
    }
    let trait_method_def_id = tcx
        .opt_associated_item(contract.def_id)?
        .trait_item_def_id()?;
    let trait_method_path = tcx.def_path_str(trait_method_def_id);
    let synthesize = |requires: Vec<String>, ensures: Vec<String>| TraitMethodContract {
        trait_def_id: origin.trait_def_id,
        method_def_id: trait_method_def_id,
        method_name: origin.trait_method_name.clone(),
        trait_path: tcx.def_path_str(origin.trait_def_id),
        requires,
        ensures,
    };
    if origin.trait_def_id.is_local() {
        // `find_trait_contracts` records every local trait method that carries
        // a contract: a local method absent from it has the empty contract.
        return Some(TraitSideContract::LocalEmpty(synthesize(
            Vec::new(),
            Vec::new(),
        )));
    }
    let spec = lookup_spec_with_extern(Some(extern_specs), &trait_method_path)
        .map(|spec| synthesize(spec.requires, spec.ensures));
    Some(TraitSideContract::External {
        trait_method_path,
        spec,
    })
}

/// How an impl of an external trait method is checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ExternalRefinementPlan {
    /// The impl declares no `requires`: the precondition direction holds for
    /// any trait precondition. No verdict and no credit (informational line).
    NoImplRequires,
    /// The impl declares `requires` and trust-wp has a spec for the trait
    /// method: check `spec requires => impl requires`, never credited.
    CheckPrecondition,
    /// The impl declares `requires` and trust-wp has no spec for the trait
    /// method: calls through the trait check nothing, so this is `unknown`
    /// and counts as an error.
    UnknownNoTraitContract,
}

pub(super) fn plan_external_refinement(
    impl_has_requires: bool,
    has_trait_spec: bool,
) -> ExternalRefinementPlan {
    match (impl_has_requires, has_trait_spec) {
        (false, _) => ExternalRefinementPlan::NoImplRequires,
        (true, true) => ExternalRefinementPlan::CheckPrecondition,
        (true, false) => ExternalRefinementPlan::UnknownNoTraitContract,
    }
}

fn apply_refinement_counts(counts: &RefinementCounts, counters: &mut VerificationCounters) {
    // Saturating: a counter that wraps would turn a rejection into an accept.
    // (Carried over from origin/main's totality hardening of the inline
    // increments this helper replaced.)
    counters.assumed = counters.assumed.saturating_add(counts.assumed_delta);
    counters.failed = counters.failed.saturating_add(counts.failed_delta);
    counters.errors = counters.errors.saturating_add(counts.error_delta);
    counters.demoted = counters.demoted.saturating_add(counts.demoted_delta);
    counters.evidence_gaps = counters
        .evidence_gaps
        .saturating_add(counts.evidence_gap_delta);
    counters.warnings = counters.warnings.saturating_add(counts.warning_delta);
    counters.encoding_errors.merge_from(&counts.encoding_errors);
}

/// Standalone refinement pass: one verdict for every trait impl method.
///
/// Independent of body verification (a trusted, skipped, failed or logic impl
/// still owes refinement). Both sides are parsed from their source clauses:
/// the effective impl contract is the impl's own clauses, or the trait's when
/// inherited (`apply_trait_contract_inheritance`), else empty; the effective
/// trait contract comes from [`resolve_trait_side_contract`].
///
/// Goal shape: trait `requires` ⇒ impl `requires`, and impl `ensures` ⇒ trait
/// `ensures`, with argument/result type invariants added by
/// `prepare_refinement_clauses`.
pub(super) fn verify_trait_impl_refinements(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    config: &VerificationRunConfig<'_>,
    trait_contract_map: &HashMap<DefId, HashMap<String, &TraitMethodContract>>,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
    counters: &mut VerificationCounters,
    undischarged: &mut crate::trait_credit::UndischargedTraitContracts,
) {
    for contract in contracts {
        if contract.trait_origin.is_none() {
            continue;
        }
        let def_path = tcx.def_path_str(contract.def_id);
        // The trait method this impl item owes a refinement goal to, when its
        // trait-level contract is one a generic call site can be handed.
        let granted_trait_method = tcx
            .opt_associated_item(contract.def_id)
            .and_then(|assoc| assoc.trait_item_def_id())
            .filter(|trait_method| config.trait_specs.contains_key(trait_method));
        let result = catch_unwind(AssertUnwindSafe(|| {
            let mut local = VerificationCounters::default();
            check_one_impl_refinement(
                tcx,
                contract,
                config,
                trait_contract_map,
                logic_fns,
                &mut local,
            );
            local
        }));
        match result {
            Ok(local) => {
                // A refinement that FAILED, errored, was refused, was
                // assumed rather than proved, or was proved without certified
                // evidence leaves the trait-level contract standing over this
                // impl. No generic caller may be handed it. An inherited
                // contract is no exception: its clauses are the trait's own
                // text on both sides (`clauses_are_the_trait_s`), so what can
                // still fail here is what types add, and a refusal is a
                // refusal.
                if let Some(trait_method) = granted_trait_method {
                    if local.failed > 0
                        || local.errors > 0
                        || local.assumed > 0
                        || local.evidence_gaps > 0
                    {
                        undischarged.record(
                            trait_method,
                            contract.def_id,
                            def_path.clone(),
                            "did not establish the refinement goal",
                        );
                    }
                }
                counters.assumed += local.assumed;
                counters.failed += local.failed;
                counters.errors += local.errors;
                counters.demoted += local.demoted;
                counters.evidence_gaps += local.evidence_gaps;
                counters.warnings += local.warnings;
                counters.encoding_errors.merge_from(&local.encoding_errors);
            }
            Err(payload) => {
                let reason = ay_core::panic_payload_to_string(payload.as_ref());
                eprintln!("trust-wp: {def_path} trait refinement error: panicked: {reason}");
                if let Some(trait_method) = granted_trait_method {
                    undischarged.record(
                        trait_method,
                        contract.def_id,
                        def_path.clone(),
                        "panicked before establishing the refinement goal",
                    );
                }
                counters.panics += 1;
                counters.errors += 1;
            }
        }
    }
}

fn check_one_impl_refinement(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    config: &VerificationRunConfig<'_>,
    trait_contract_map: &HashMap<DefId, HashMap<String, &TraitMethodContract>>,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
    counters: &mut VerificationCounters,
) {
    let def_path = tcx.def_path_str(contract.def_id);
    let loc = format!("{:?}", tcx.def_span(contract.def_id));

    // An impl whose `Self` type (or a trait type argument) exposes
    // interior-mutable memory cannot refine a trait contract: generic callers
    // of the trait model shared access to `Self` as an unchanging value (the
    // structural generic rule of the `!Freeze` write lane), which such an impl
    // breaks (`impl Rd for Cell<u8>` whose `wr(&self)` writes the cell a logic
    // `m(self)` reads). Fail closed: no refinement credit.
    if let Some(impl_def_id) = tcx.opt_parent(contract.def_id).filter(|parent| {
        matches!(
            tcx.def_kind(*parent),
            rustc_hir::def::DefKind::Impl { of_trait: true }
        )
    }) {
        let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, impl_def_id);
        let trait_ref = tcx.impl_trait_ref(impl_def_id).skip_binder();
        if trait_ref.args.types().any(|ty| {
            crate::mir_analysis::extract::ty_exposes_interior_mutability(tcx, typing_env, ty)
        }) {
            eprintln!(
                "trust-wp: {def_path} refinement unknown (interior-mutable Self: generic callers \
                 of the trait treat shared access as preserving the value)"
            );
            eprintln!("  at {loc}");
            counters.errors += 1;
            return;
        }
    }

    let Some(trait_side) =
        resolve_trait_side_contract(tcx, contract, trait_contract_map, config.extern_specs)
    else {
        eprintln!("trust-wp: {def_path} refinement unknown (trait method not resolvable)");
        eprintln!("  at {loc}");
        counters.errors += 1;
        return;
    };
    let owned_trait_contract;
    let (trait_contract, precondition_only): (&TraitMethodContract, bool) = match trait_side {
        TraitSideContract::Declared(trait_contract) => (trait_contract, false),
        TraitSideContract::LocalEmpty(trait_contract) => {
            owned_trait_contract = trait_contract;
            (&owned_trait_contract, false)
        }
        TraitSideContract::External {
            trait_method_path,
            spec,
        } => match plan_external_refinement(!contract.requires.is_empty(), spec.is_some()) {
            ExternalRefinementPlan::NoImplRequires => {
                // Creusot states this goal over the trait-level contract of
                // an external trait, which trust-wp does not model; its
                // call-site specs are not that contract. Say so, never credit.
                eprintln!(
                    "trust-wp: {def_path} refinement not checked: impl of external trait \
                     method `{trait_method_path}` declares no requires (precondition \
                     direction holds); postcondition direction has no trait-level contract"
                );
                return;
            }
            ExternalRefinementPlan::UnknownNoTraitContract => {
                eprintln!("trust-wp: {def_path} refinement unknown (no trait contract)");
                eprintln!("  trait method: {trait_method_path}");
                eprintln!("  check: trait precondition implies impl precondition");
                eprintln!("  at {loc}");
                counters.errors += 1;
                return;
            }
            ExternalRefinementPlan::CheckPrecondition => {
                owned_trait_contract = spec.expect("planned only with a trait spec");
                (&owned_trait_contract, true)
            }
        },
    };

    // An inherited contract is checked as the trait's own text, renamed to the
    // impl's parameter names position by position — exactly what
    // `restate_inherited_clauses` gave the impl's body to owe, before the
    // trait-scope resolution that only the grant and the body read. The two
    // sides are then the same clauses, so they are premises and never goals;
    // what types add (invariants, ranges) is still checked. Where the renaming is
    // refused the body owes an unstatable contract, and the trait's text is
    // compared as written, so the refusal is recorded here as well.
    //
    // Only for a trait declared directly in a module (D-113): the trait-scope
    // resolution looks names up in the trait's MODULE, so for a trait declared
    // in a block both sides read one text with a block item's name read as the
    // module's, and the scope closure's refusal is all that stands in the way
    // (trait_inherited_clause_block_local_name_granted.rs).
    let inherited = contract.trait_origin.as_ref().is_some_and(|origin| {
        origin.inherits_clauses
            && matches!(
                tcx.def_kind(tcx.parent(origin.trait_def_id)),
                rustc_hir::def::DefKind::Mod
            )
    }) && !precondition_only;
    let arg_names = get_arg_names_from_def_id(tcx, contract.def_id).unwrap_or_default();
    let renamed_trait_text = inherited
        .then(|| {
            let renames = crate::callbacks::discovery::inherited_param_renames(
                tcx,
                trait_contract.method_def_id,
                contract.def_id,
            );
            let rename = |clauses: &[String]| -> Option<Vec<String>> {
                clauses
                    .iter()
                    .map(|clause| {
                        crate::callbacks::discovery::rename_inherited_params(clause, &renames)
                    })
                    .collect()
            };
            rename(&trait_contract.requires).zip(rename(&trait_contract.ensures))
        })
        .flatten();
    let clauses_are_the_trait_s = renamed_trait_text.is_some();
    let (impl_requires_text, impl_ensures_text): (&[String], &[String]) =
        match (&renamed_trait_text, inherited) {
            (Some((requires, ensures)), _) => (requires, ensures),
            (None, true) => (&trait_contract.requires, &trait_contract.ensures),
            (None, false) => (&contract.requires, &contract.ensures),
        };

    let base_requires = match parse_contract_clauses(impl_requires_text, "requires", &def_path) {
        Ok(exprs) => exprs,
        Err(e) => {
            eprintln!("trust-wp: {def_path} trait refinement error: failed to parse requires: {e}");
            counters.errors += 1;
            return;
        }
    };
    let base_ensures = match parse_contract_clauses(impl_ensures_text, "ensures", &def_path) {
        Ok(exprs) => exprs,
        Err(e) => {
            eprintln!("trust-wp: {def_path} trait refinement error: failed to parse ensures: {e}");
            counters.errors += 1;
            return;
        }
    };

    let logic_fns_opt = (!logic_fns.is_empty()).then_some(logic_fns);
    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
    let qualified_def_path = format!("{local_crate_name}::{def_path}");
    let mode_overrides;
    let mode_overrides_opt = if logic_fns
        .iter()
        .any(|lf| matches!(lf.mode(), LogicMode::OpenSelf | LogicMode::Default))
    {
        mode_overrides = scope_logic_fn_modes(logic_fns, &qualified_def_path);
        Some(mode_overrides.as_slice())
    } else {
        None
    };
    let adt_decls = build_adt_decls(tcx, contract.def_id);
    let adt_decls_opt = (!adt_decls.is_empty()).then_some(&adt_decls);

    let refinement_req = TraitRefinementRequest {
        impl_def_id: contract.def_id,
        impl_arg_names: &arg_names,
        trait_contract,
        base_requires: &base_requires,
        base_ensures: &base_ensures,
        impl_requires_text,
        impl_ensures_text,
        type_invariant_defs: config.type_invariant_defs,
        logic_fns_opt,
        mode_overrides_opt,
        adt_decls: adt_decls_opt,
        track_level: config.track_level,
        def_path: &def_path,
        loc: &loc,
        verbose: config.verbose,
        precondition_only,
        clauses_are_the_trait_s,
        timeout: config.timeout,
    };
    let counts = verify_trait_refinement(tcx, &refinement_req);
    apply_refinement_counts(&counts, counters);
}
