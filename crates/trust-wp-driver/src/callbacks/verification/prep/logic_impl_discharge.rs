// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The obligation a trait LOGIC method's postcondition grant rests on.
//!
//! A contracted trait logic method `Tr::m` is a declaration symbol whose
//! `ensures` is an axiom: a generic consumer (`t.m() >= 0` for `T: Tr`) is
//! handed it for every `Self`. That grant is only true if every implementation
//! establishes the postcondition at its own `Self`. Nothing asked: an impl
//! that declares no clause has no `ensures` of its own for the logic pass to
//! check, and the refinement check compares clause text, not bodies
//! (trait_logic_method_ensures_unowed_by_logic_impl.rs).
//!
//! Here each local logic impl `I` of such a method `D` owes, over `D`'s own
//! parsed clauses (the axiom's formulas), `D.requires => D.ensures` with
//! `result := I(params)`. `I`'s defining axiom and its own verified `ensures`
//! are available to the proof, so the goal is what the grant says about the
//! code that defines `I`. An impl that does not discharge it withdraws `D`'s
//! axiom for everyone, the way an unproved logic postcondition is withdrawn.
//!
//! `D`'s clauses are read at `I` first: a call of a trait declaration whose
//! receiver has a concrete type at `I` (`assoc.inv()` with `assoc:
//! Self::Assoc`) is the implementation rustc selects for that type there
//! (`instantiate_trait_decl_calls_at_impl`), which is what the grant says of
//! this `Self`. Fail closed on the rest: the clauses must then name no
//! declaration symbol, no unresolved call and no method call. Such a name
//! stands for the method at an ABSTRACT `Self`, and read as the declaration it
//! carries the declaration's own axiom, which is itself a grant resting on
//! this impl — circular. An implementation that is not a logic function the
//! logic model can read discharges nothing either.

use std::collections::{HashMap, HashSet};

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE},
};
use rustc_middle::ty::{AssocContainer, TyCtxt};
use trust_wp_ay::{
    verify_function_with_modes_outcome, VerificationOutcome, VerificationRequest,
    VerificationResult,
};
use trust_wp_core::{
    formula::{CaptureAvoidingSubstOptions, PureExpr},
    logic::{
        identity::{
            is_refused_logic_fn_marker, logic_fn_identity_registry, LogicFnOwnerKind,
            LOGIC_FN_EXTERN_DECL_PREFIX,
        },
        LogicFnDef,
    },
};

use super::{
    super::{
        super::{
            helpers::scope_logic_fn_modes,
            reporting::{verified_evidence_gap_reason, VerificationCounters},
        },
        logic_fn_verify::{LogicCredits, VerifyConfig},
    },
    logic_fn_catalog::filter_downstream_logic_fns,
};
use crate::logic::identity::instantiate_trait_decl_calls_at_impl;

/// One trait logic method with a postcondition and the local impls that owe it.
struct Owed<'a> {
    decl_id: DefId,
    decl: &'a LogicFnDef,
    impls: Vec<(DefId, Option<&'a LogicFnDef>)>,
}

/// Crate-qualified path of a local item, the key `LogicFnDef::full_path` uses.
fn full_path(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    format!(
        "{}::{}",
        tcx.crate_name(LOCAL_CRATE),
        tcx.def_path_str(def_id)
    )
}

/// Bodyless, non-law trait logic methods: their postcondition is owed by the
/// implementations (this module), and the logic pass has no body to check it
/// against — the placeholder a declaration carries is not one.
pub(in crate::callbacks) fn impl_owed_trait_logic_decls(
    tcx: TyCtxt<'_>,
    logic_fns: &[LogicFnDef],
) -> HashSet<String> {
    let by_path: HashMap<&str, &LogicFnDef> =
        logic_fns.iter().map(|lf| (lf.full_path(), lf)).collect();
    tcx.iter_local_def_id()
        .map(|local| local.to_def_id())
        .filter(|def_id| tcx.def_kind(*def_id) == DefKind::AssocFn)
        .filter(|def_id| {
            tcx.opt_associated_item(*def_id).is_some_and(|assoc| {
                matches!(assoc.container, AssocContainer::Trait)
                    && !tcx.defaultness(*def_id).has_value()
            })
        })
        .map(|def_id| full_path(tcx, def_id))
        .filter(|path| {
            by_path
                .get(path.as_str())
                .is_some_and(|lf| !lf.ensures().is_empty() && !lf.is_law() && !lf.is_trusted())
        })
        .collect()
}

fn collect_owed<'a>(tcx: TyCtxt<'_>, logic_fns: &'a [LogicFnDef]) -> Vec<Owed<'a>> {
    let by_path: HashMap<&str, &LogicFnDef> =
        logic_fns.iter().map(|lf| (lf.full_path(), lf)).collect();
    let mut owed: Vec<Owed<'a>> = Vec::new();
    for local in tcx.iter_local_def_id() {
        let decl_id = local.to_def_id();
        if tcx.def_kind(decl_id) != DefKind::AssocFn {
            continue;
        }
        let Some(assoc) = tcx.opt_associated_item(decl_id) else {
            continue;
        };
        if !matches!(assoc.container, AssocContainer::Trait) {
            continue;
        }
        let Some(decl) = by_path.get(full_path(tcx, decl_id).as_str()).copied() else {
            continue;
        };
        // A law is proved generically (same-trait bodies hidden) and an impl
        // law is its own item; `#[trusted]` is the user's request to take the
        // clause on faith, inherited by every impl.
        if decl.ensures().is_empty() || decl.is_law() || decl.is_trusted() {
            continue;
        }
        let trait_id = tcx.parent(decl_id);
        let mut impls = Vec::new();
        for impl_id in tcx
            .iter_local_def_id()
            .map(|local| local.to_def_id())
            .filter(|def_id| matches!(tcx.def_kind(*def_id), DefKind::Impl { of_trait: true }))
            .filter(|impl_id| tcx.impl_opt_trait_id(*impl_id) == Some(trait_id))
        {
            let Some(item) = tcx
                .associated_items(impl_id)
                .in_definition_order()
                .find(|item| item.trait_item_def_id() == Some(decl_id))
            else {
                // The impl runs the trait's default body, which the logic pass
                // verifies against this postcondition.
                continue;
            };
            let def = by_path.get(full_path(tcx, item.def_id).as_str()).copied();
            impls.push((item.def_id, def));
        }
        if !impls.is_empty() {
            owed.push(Owed {
                decl_id,
                decl,
                impls,
            });
        }
    }
    owed
}

/// Names of every logic function declared in a trait: a call to one stands
/// for the method at an abstract `Self`.
fn trait_decl_names(tcx: TyCtxt<'_>, logic_fns: &[LogicFnDef]) -> HashSet<String> {
    let trait_item_paths: HashSet<String> = tcx
        .iter_local_def_id()
        .map(|local| local.to_def_id())
        .filter(|def_id| tcx.def_kind(*def_id) == DefKind::AssocFn)
        .filter(|def_id| {
            tcx.opt_associated_item(*def_id)
                .is_some_and(|assoc| matches!(assoc.container, AssocContainer::Trait))
        })
        .map(|def_id| full_path(tcx, def_id))
        .collect();
    logic_fns
        .iter()
        .filter(|lf| trait_item_paths.contains(lf.full_path()))
        .flat_map(|lf| [lf.name().to_string(), lf.short_name().to_string()])
        .collect()
}

/// The first name in `expr` whose meaning at the impl is not the meaning the
/// declaration's axiom gives it.
fn abstract_self_name(expr: &PureExpr, decl_names: &HashSet<String>) -> Option<String> {
    let registry = logic_fn_identity_registry();
    let mut found = None;
    expr.for_each_recursive(|node| {
        if found.is_some() {
            return;
        }
        match node {
            PureExpr::MethodCall { method, .. } => {
                found = Some(format!("method call `.{method}(..)`"))
            }
            PureExpr::LogicFnCall { name, .. } => {
                let is_decl = decl_names.contains(name)
                    || name.starts_with(LOGIC_FN_EXTERN_DECL_PREFIX)
                    || is_refused_logic_fn_marker(name)
                    || registry.as_ref().is_some_and(|registry| {
                        registry
                            .member(name)
                            .is_some_and(|member| member.kind == LogicFnOwnerKind::TraitDecl)
                            || registry.unresolved_family_for_call(name).is_some()
                    });
                if is_decl {
                    found = Some(format!("call `{name}(..)`"));
                }
            }
            _ => {}
        }
    });
    found
}

/// How one impl came out.
enum Discharge {
    Proved,
    Refused(String),
    Outcome(Result<VerificationOutcome, String>),
}

fn check_one(
    tcx: TyCtxt<'_>,
    cfg: &VerifyConfig<'_>,
    available: &[LogicFnDef],
    (decl_id, decl): (DefId, &LogicFnDef),
    (impl_id, imp): (DefId, &LogicFnDef),
    decl_names: &HashSet<String>,
) -> Discharge {
    if decl.params().len() != imp.params().len() {
        return Discharge::Refused(format!(
            "the declaration has {} parameters and the implementation {}",
            decl.params().len(),
            imp.params().len()
        ));
    }
    // The grant's clauses at this impl: a declaration call whose receiver is
    // concrete here becomes the implementation rustc selects for it. One that
    // does not stays a declaration symbol, and the check below refuses it.
    let at_impl = |clause: &PureExpr| {
        instantiate_trait_decl_calls_at_impl(tcx, decl_id, impl_id, decl.params(), clause)
    };
    let decl_requires: Vec<PureExpr> = decl.requires().iter().map(at_impl).collect();
    let decl_ensures: Vec<PureExpr> = decl.ensures().iter().map(at_impl).collect();
    if let Some(name) = decl_requires
        .iter()
        .chain(&decl_ensures)
        .find_map(|clause| abstract_self_name(clause, decl_names))
    {
        return Discharge::Refused(format!(
            "the postcondition names {name}, which stands for the method at an abstract `Self`"
        ));
    }
    // The declaration's clauses over the impl's parameter names.
    let renaming: HashMap<String, PureExpr> = decl
        .params()
        .iter()
        .zip(imp.params())
        .enumerate()
        .filter(|(_, (from, to))| from != to)
        .map(|(index, (from, to))| {
            let sort = imp.param_sorts().get(index).cloned().flatten();
            (from.clone(), PureExpr::Var(to.clone(), sort))
        })
        .collect();
    let rename = |clause: &PureExpr| {
        if renaming.is_empty() {
            clause.clone()
        } else {
            clause.substitute_capture_avoiding(&renaming, &CaptureAvoidingSubstOptions::default())
        }
    };
    let requires: Vec<PureExpr> = decl_requires.iter().map(rename).collect();
    let ensures: Vec<PureExpr> = decl_ensures.iter().map(rename).collect();
    let applied = PureExpr::LogicFnCall {
        name: imp.name().to_string(),
        args: imp
            .params()
            .iter()
            .enumerate()
            .map(|(index, param)| {
                PureExpr::Var(
                    param.clone(),
                    imp.param_sorts().get(index).cloned().flatten(),
                )
            })
            .collect(),
    };
    // The impl's own module sees its body; everything else keeps its scope.
    let overrides = scope_logic_fn_modes(available, imp.full_path());
    let outcome = verify_function_with_modes_outcome(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&applied))
            .logic_fns(Some(available))
            .mode_overrides(Some(overrides.as_slice()))
            .type_invariants(cfg.type_invariants_opt)
            .track(Some(cfg.track_level))
            .timeout(cfg.timeout)
            .adt_field_ranges(cfg.adt_field_ranges.clone())
            .adt_decls(cfg.adt_decls.clone()),
    );
    match outcome {
        Ok(outcome)
            if matches!(outcome.result, VerificationResult::Verified(_))
                && verified_evidence_gap_reason(&outcome).is_none() =>
        {
            Discharge::Proved
        }
        Ok(outcome) => Discharge::Outcome(Ok(outcome)),
        Err(error) => Discharge::Outcome(Err(error.to_string())),
    }
}

/// Check every local logic impl of a contracted trait logic method against
/// the postcondition its declaration's axiom grants, withdraw the axiom of
/// every declaration some impl does not discharge, and return the impls that
/// were checked and did not. An impl this check does not own (of a law, of a
/// `#[trusted]` declaration) is in neither set.
///
/// Runs after the logic pass, over the axioms that survived it. A check that
/// passed on an axiom a later check withdraws is re-run without it, until
/// nothing more is withdrawn. The logic pass's own credits are held to the
/// same rule at the start of every round (`LogicCredits::withdraw_stale`): a
/// logic function proved on a grant withdrawn here loses its credit and its
/// axiom, and the checks that follow run without it.
pub(in crate::callbacks) fn verify_logic_impls_discharge_trait_postconditions(
    tcx: TyCtxt<'_>,
    cfg: &VerifyConfig<'_>,
    counters: &mut VerificationCounters,
    unverified_axioms: &mut HashSet<String>,
    logic_credits: &mut LogicCredits,
) -> HashSet<DefId> {
    let mut undischarged = HashSet::new();
    let owed = collect_owed(tcx, cfg.logic_fns);
    if owed.is_empty() {
        logic_credits.withdraw_stale(cfg.logic_fns, unverified_axioms, counters);
        return undischarged;
    }
    let decl_names = trait_decl_names(tcx, cfg.logic_fns);
    // Each round checks every impl of every declaration still standing,
    // over the axioms still standing; a withdrawal starts the next round.
    let discharged = loop {
        logic_credits.withdraw_stale(cfg.logic_fns, unverified_axioms, counters);
        let available = filter_downstream_logic_fns(cfg.logic_fns, unverified_axioms);
        let mut discharged: Vec<(DefId, DefId)> = Vec::new();
        let mut withdrawn: Option<String> = None;
        'decls: for entry in &owed {
            if unverified_axioms.contains(entry.decl.full_path()) {
                continue;
            }
            for (impl_id, imp) in &entry.impls {
                let result = match imp {
                    Some(imp) => check_one(
                        tcx,
                        cfg,
                        &available,
                        (entry.decl_id, entry.decl),
                        (*impl_id, imp),
                        &decl_names,
                    ),
                    None => Discharge::Refused(
                        "it is not a logic function the logic model can read".to_string(),
                    ),
                };
                if matches!(result, Discharge::Proved) {
                    discharged.push((*impl_id, entry.decl_id));
                    continue;
                }
                report_undischarged(tcx, *impl_id, entry.decl_id, result, counters);
                undischarged.insert(*impl_id);
                withdrawn = Some(entry.decl.full_path().to_owned());
                break 'decls;
            }
        }
        match withdrawn {
            Some(path) => {
                counters.warnings += 1;
                unverified_axioms.insert(path);
            }
            None => break discharged,
        }
    };
    for (impl_id, decl_id) in &discharged {
        eprintln!(
            "trust-wp: {} establishes the postcondition of trait logic method `{}`",
            tcx.def_path_str(*impl_id),
            tcx.def_path_str(*decl_id)
        );
    }
    undischarged
}

/// Print and count one impl that does not discharge its declaration's
/// postcondition, whose axiom is withdrawn for it.
fn report_undischarged(
    tcx: TyCtxt<'_>,
    impl_id: DefId,
    decl_id: DefId,
    result: Discharge,
    counters: &mut VerificationCounters,
) {
    let impl_path = tcx.def_path_str(impl_id);
    let decl_path = tcx.def_path_str(decl_id);
    let reason = match result {
        Discharge::Proved => return,
        Discharge::Refused(why) => {
            counters.errors += 1;
            eprintln!(
                "trust-wp: {impl_path} error: the postcondition of trait logic method \
                 `{decl_path}` cannot be checked against it: {why}"
            );
            "was not checked against"
        }
        Discharge::Outcome(Ok(VerificationOutcome {
            result: VerificationResult::Failed(_),
            ..
        })) => {
            counters.failed += 1;
            eprintln!(
                "trust-wp: {impl_path} FAILED ✗ (postcondition of trait logic method \
                 `{decl_path}`)"
            );
            "refutes"
        }
        Discharge::Outcome(Ok(outcome)) => {
            if let Some(gap) = verified_evidence_gap_reason(&outcome) {
                counters.evidence_gaps += 1;
                counters.warnings += 1;
                eprintln!(
                    "trust-wp: {impl_path} evidence gap ({gap}) on the postcondition of trait \
                     logic method `{decl_path}`"
                );
                "has no certified proof of"
            } else {
                counters.errors += 1;
                eprintln!(
                    "trust-wp: {impl_path} unknown (postcondition of trait logic method \
                     `{decl_path}` not proved)"
                );
                "did not prove"
            }
        }
        Discharge::Outcome(Err(error)) => {
            counters.errors += 1;
            eprintln!(
                "trust-wp: {impl_path} error: postcondition of trait logic method \
                 `{decl_path}`: {error}"
            );
            "could not state"
        }
    };
    eprintln!(
        "trust-wp: {decl_path} postcondition withheld from callers: `{impl_path}` {reason} it"
    );
}
