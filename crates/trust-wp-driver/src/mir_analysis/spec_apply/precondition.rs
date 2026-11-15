// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Precondition obligation generation at call sites.
//!
//! For each `requires` clause of the called function, substitutes the actual
//! call-site arguments and pushes the resulting expression as a proof obligation.

use std::collections::HashMap;

use tracing::debug;
use trust_wp_core::formula::PureExpr;

use super::{
    applied_opaque_callable_param, insert_std_symbolic_substitutions, substitutions_for_expr,
    unresolved_symbolic_names, warn_unresolved_names, TranslatedArg,
};
use crate::mir_analysis::effects::{CallEffects, DroppedClauseKind};

/// Generate call-site precondition obligations into explicit `CallEffects`.
///
/// Dropped preconditions generate synthetic `false` obligations in the
/// inner function (#1739).
pub(in crate::mir_analysis) fn apply_preconditions_with_effects(
    requires: &[String],
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    effects: &mut CallEffects,
) {
    apply_preconditions_with_self_inner(requires, translated_args, param_names, None, effects);
}

/// Generate call-site precondition obligations with optional explicit `self`
/// into explicit `CallEffects`.
///
/// Dropped preconditions generate synthetic `false` obligations in the
/// inner function (#1739).
pub(in crate::mir_analysis) fn apply_preconditions_with_self_and_effects(
    requires: &[String],
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    explicit_self_expr: Option<&PureExpr>,
    effects: &mut CallEffects,
) {
    apply_preconditions_with_self_inner(
        requires,
        translated_args,
        param_names,
        explicit_self_expr,
        effects,
    );
}

/// Generate precondition obligations into a `CallEffects` (non-thread-local variant).
///
/// Same logic as `apply_preconditions` but collects into explicit `CallEffects`
/// instead of an implicit side channel. Callers can extract
/// `effects.obligations` afterward for further processing (e.g., path-condition
/// wrapping in loop body extraction).
pub(in crate::mir_analysis) fn collect_precondition_obligations(
    requires: &[String],
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    effects: &mut CallEffects,
) {
    collect_precondition_obligations_with_self(
        requires,
        translated_args,
        param_names,
        effects,
        None,
    );
}

/// Generate precondition obligations with optional explicit `self`.
pub(in crate::mir_analysis) fn collect_precondition_obligations_with_self(
    requires: &[String],
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    effects: &mut CallEffects,
    explicit_self_expr: Option<&PureExpr>,
) {
    // Delegate to the shared inner function which handles provenance
    // recording and fail-closed obligation insertion (#1739).
    apply_preconditions_with_self_inner(
        requires,
        translated_args,
        param_names,
        explicit_self_expr,
        effects,
    );
}

/// Inner implementation for precondition obligation generation.
///
/// Dropped preconditions are recorded via `effects.record_dropped_clause()` which
/// pushes both provenance and a synthetic `false` obligation (#1739).
fn apply_preconditions_with_self_inner(
    requires: &[String],
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    explicit_self_expr: Option<&PureExpr>,
    effects: &mut CallEffects,
) {
    if requires.is_empty() {
        return;
    }

    // Build the same substitution map as apply_postconditions (minus result)
    let mut base_substitutions: HashMap<String, PureExpr> = HashMap::new();

    insert_std_symbolic_substitutions(&mut base_substitutions, translated_args);

    if let Some(names) = param_names {
        for (idx, name) in names.iter().enumerate() {
            if name == "self" {
                continue;
            }
            if let Some(arg) = translated_args.get(idx) {
                base_substitutions.insert(name.clone(), arg.expr.clone());
            }
        }
    }

    // Accept fallback args as `self` for preconditions, matching
    // the postcondition behavior. (#1572)
    let self_arg_expr = explicit_self_expr
        .cloned()
        .or_else(|| translated_args.first().map(|arg| arg.expr.clone()));

    for req_str in requires {
        match trust_wp_core::contract_parser::parse_contract(req_str) {
            Ok(req_expr) => {
                // Fail closed: a precondition that applies an opaque callable
                // cannot be discharged by substituting the argument, and
                // omitting it would drop an obligation.
                if let Some(name) = applied_opaque_callable_param(
                    &req_expr,
                    translated_args,
                    param_names,
                    self_arg_expr.is_some(),
                ) {
                    debug!(
                        "trust-wp: precondition `{req_str}` cannot be applied: it applies \
                         `{name}`, which is bound to an opaque callable argument"
                    );
                    effects.record_dropped_clause(
                        DroppedClauseKind::Precondition,
                        req_str.clone(),
                        format!("applies opaque callable parameter: {name}"),
                    );
                    continue;
                }
                // `^x.m`, `^*x`, `^x[0]` of a callee parameter reads the
                // final value of a borrow the argument's referent holds,
                // which the callee's own lane refuses (D-183); this site
                // cannot read the callee's parameter types, so every
                // parameter is read as a reference one and such a clause is
                // dropped, which leaves a `false` obligation (#1739).
                if let Some(names) = param_names {
                    let reference = |name: &str| {
                        names
                            .iter()
                            .any(|param| param == name)
                            .then_some(trust_wp_core::formula::elaborate::ParamReference::Mutable)
                    };
                    if let Some(reason) =
                        trust_wp_core::formula::elaborate::first_final_held_through_a_reference_parameter(
                            &req_expr,
                            &reference,
                            &trust_wp_core::logic::final_reads::FinalReaders::default(),
                        )
                    {
                        effects.record_dropped_clause(
                            DroppedClauseKind::Precondition,
                            req_str.clone(),
                            format!("final value refused: {reason}"),
                        );
                        continue;
                    }
                }
                let substitutions = substitutions_for_expr(
                    req_str,
                    &req_expr,
                    &base_substitutions,
                    self_arg_expr.as_ref(),
                );
                let unresolved = unresolved_symbolic_names(&req_expr, &substitutions, param_names);
                if unresolved.is_empty() {
                    let substituted = req_expr.substitute(&substitutions);
                    // D-27: a callee's own `#[requires(false)]` substitutes to
                    // the literal `false`, which is exactly what an unmodelled
                    // construct's fail-closed marker is spelled as. This one is
                    // a clause somebody WROTE and its refutation must keep its
                    // FAILED, so it is counted here, where the provenance is
                    // known.
                    effects.record_user_written_obligation(substituted);
                } else {
                    warn_unresolved_names(req_str, &unresolved, "precondition obligation");
                    let names: Vec<&str> = unresolved.iter().map(String::as_str).collect();
                    effects.record_dropped_clause(
                        DroppedClauseKind::Precondition,
                        req_str.clone(),
                        format!("unresolved symbolic names: {}", names.join(", ")),
                    );
                }
            }
            Err(e) => {
                crate::result_protocol_state::record_parse_error();
                let reason = format!("parse error: {e}");
                debug!(
                    "trust-wp: error: failed to parse requires clause `{req_str}`: {e} \
                     (verification will fail — fail-closed #1739)"
                );
                effects.record_dropped_clause(
                    DroppedClauseKind::Precondition,
                    req_str.clone(),
                    reason,
                );
            }
        }
    }
}

/// Generate call-site obligations for the callee's SYNTHESIZED type-invariant
/// preconditions.
///
/// These clauses are the other half of the grant the callee's own body enjoys:
/// `clause_enrichment` hands the callee `inv(param)` as a premise, and this is
/// the code that makes a caller pay for it. Both read the same
/// `StdSpec::inv_requires` vector, so the two can never state different
/// clauses.
///
/// The clauses arrive already structured (`PureExpr`), so they skip the
/// contract parser entirely and go straight to the substitution the string
/// lane performs. That is deliberate: `PureExpr::Match` (enum decomposition)
/// and tuple field access have no faithful contract-source spelling, so a
/// round trip through text would silently drop exactly the structural shapes,
/// leaving the free grant open for them.
///
/// Fail closed: a clause whose parameter cannot be resolved to a call-site
/// argument takes the dropped-clause path (synthetic `false`), never a skip.
/// A skipped invariant obligation is the free grant wearing a coverage badge.
pub(in crate::mir_analysis) fn apply_invariant_preconditions_with_effects(
    inv_requires: &[PureExpr],
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    explicit_self_expr: Option<&PureExpr>,
    effects: &mut CallEffects,
) {
    if inv_requires.is_empty() {
        return;
    }

    let mut base_substitutions: HashMap<String, PureExpr> = HashMap::new();
    insert_std_symbolic_substitutions(&mut base_substitutions, translated_args);
    if let Some(names) = param_names {
        for (idx, name) in names.iter().enumerate() {
            if name == "self" {
                continue;
            }
            if let Some(arg) = translated_args.get(idx) {
                base_substitutions.insert(name.clone(), arg.expr.clone());
            }
        }
    }
    let self_arg_expr = explicit_self_expr
        .cloned()
        .or_else(|| translated_args.first().map(|arg| arg.expr.clone()));
    if let Some(self_expr) = self_arg_expr {
        base_substitutions.insert("self".to_string(), self_expr);
    }

    for clause in inv_requires {
        // Stricter than the string lane's `unresolved_symbolic_names`, which
        // only flags names it recognises as parameter-like. A synthesized
        // invariant clause mentions nothing BUT the callee's parameters, so
        // any surviving free name means the call-site binding was not found
        // and the obligation would quantify over a symbol the caller never
        // constrains.
        let unresolved: Vec<String> = {
            let mut names: Vec<String> = clause
                .free_vars()
                .into_iter()
                .filter(|name| !base_substitutions.contains_key(name))
                .collect();
            names.sort_unstable();
            names
        };
        if unresolved.is_empty() {
            effects.record_user_written_obligation(clause.substitute(&base_substitutions));
        } else {
            debug!(
                "trust-wp: callee type-invariant obligation dropped: unresolved [{}]",
                unresolved.join(", ")
            );
            effects.record_dropped_clause(
                DroppedClauseKind::Precondition,
                format!("callee type invariant: {clause:?}"),
                format!("unresolved parameter names: {}", unresolved.join(", ")),
            );
        }
    }
}
