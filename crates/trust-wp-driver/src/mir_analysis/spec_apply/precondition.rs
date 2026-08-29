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
    insert_std_symbolic_substitutions, substitutions_for_expr, unresolved_symbolic_names,
    warn_unresolved_names, TranslatedArg,
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
                let substitutions = substitutions_for_expr(
                    req_str,
                    &req_expr,
                    &base_substitutions,
                    self_arg_expr.as_ref(),
                );
                let unresolved = unresolved_symbolic_names(&req_expr, &substitutions, param_names);
                if unresolved.is_empty() {
                    let substituted = req_expr.substitute(&substitutions);
                    effects.obligations.push(substituted);
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
