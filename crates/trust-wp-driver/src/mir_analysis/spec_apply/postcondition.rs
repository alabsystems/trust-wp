// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Postcondition specification application at call sites.
//!
//! Contains the postcondition application pipeline: parsing ensures clauses,
//! extracting direct result constraints, and recording predicate assumptions.

use std::collections::HashMap;

use tracing::debug;
use trust_wp_core::formula::{
    elaborate::{postcondition_at_a_call, Signature},
    PureExpr,
};

use super::{
    applied_opaque_callable_param, insert_std_symbolic_substitutions, names_of_stale_arguments,
    reads_a_stale_argument, receiver_state::connect_final_receiver_state_witness,
    result_extraction::try_extract_result_expr, substitutions_for_expr, unresolved_symbolic_names,
    warn_unresolved_names, TranslatedArg,
};
use crate::mir_analysis::effects::{CallEffects, DroppedClauseKind};

/// Apply postconditions and record side effects into explicit `CallEffects`.
///
/// Dropped postconditions generate synthetic `false` obligations to enforce
/// fail-closed semantics (#1739).
pub(in crate::mir_analysis) fn apply_postconditions_with_effects(
    ensures: &[String],
    callee: &Signature,
    result_var: &PureExpr,
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    effects: &mut CallEffects,
    record_predicate_assumptions: bool,
) -> PureExpr {
    // record_dropped_clause() in the inner function now handles both
    // provenance recording and synthetic false obligation insertion (#1739).
    apply_postconditions_with_self_inner(
        ensures,
        callee,
        result_var,
        translated_args,
        param_names,
        None,
        effects,
        record_predicate_assumptions,
        true,
    )
}

/// Apply postconditions for loop body extraction with explicit effect sink.
///
/// Like `apply_postconditions_with_effects` but never records predicate
/// assumptions (avoids double-pushing in loop body context). Matches
/// `result@ == <expr>` patterns. (#1463, #1673)
///
/// Dropped postconditions generate synthetic `false` obligations (#1739).
pub(in crate::mir_analysis) fn apply_postconditions_for_loop_body_with_effects(
    ensures: &[String],
    callee: &Signature,
    result_var: &PureExpr,
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    effects: &mut CallEffects,
) -> PureExpr {
    apply_postconditions_with_self_inner(
        ensures,
        callee,
        result_var,
        translated_args,
        param_names,
        None,
        effects,
        false, // Never record predicate assumptions in loop body context
        true,  // Match result@ == <expr> patterns
    )
}

/// Apply postconditions with explicit `self` binding and explicit effect sink.
///
/// Dropped postconditions generate synthetic `false` obligations via
/// `record_dropped_clause()` in the inner function (#1739).
pub(in crate::mir_analysis) fn apply_postconditions_with_self_and_effects(
    ensures: &[String],
    callee: &Signature,
    result_var: &PureExpr,
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    explicit_self_expr: Option<&PureExpr>,
    effects: &mut CallEffects,
) -> PureExpr {
    apply_postconditions_with_self_inner(
        ensures,
        callee,
        result_var,
        translated_args,
        param_names,
        explicit_self_expr,
        effects,
        true,
        true,
    )
}

/// Inner implementation: apply postconditions with configurable assumption recording.
///
/// When `record_assumptions` is `false`, predicate-style postconditions (those that
/// don't match `result == <expr>`) are still substituted and resolved, but they are
/// NOT recorded into `effects.assumptions`. This prevents the substitution-extraction
/// pass (pass 1) from double-pushing assumptions that the full extraction pass
/// (pass 2) will record correctly with advanced receiver state (#1310).
///
/// When `match_view_result` is `true`, also matches `result@ == <expr>` patterns
/// (view of result). All public callers now pass `true` since #1673 — the view
/// operator is transparent for primitive return types, and ay's sort unification
/// catches any type mismatches for non-primitive returns. (#1463, #1673)
///
/// Dropped postconditions are recorded via `effects.record_dropped_clause()` which
/// pushes both provenance and a synthetic `false` obligation (#1739).
#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
fn apply_postconditions_with_self_inner(
    ensures: &[String],
    callee: &Signature,
    result_var: &PureExpr,
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    explicit_self_expr: Option<&PureExpr>,
    effects: &mut CallEffects,
    record_assumptions: bool,
    match_view_result: bool,
) -> PureExpr {
    // Build base substitution map for symbolic names.
    //
    // Priority rules:
    // 1. "result" always maps to the return value (never overridden by param_names)
    // 2. Positional aliases are defaults for std specs; param_names override
    //    them when present (user specs use actual parameter names)
    // 3. "self" maps from args[0] per-clause (for deref_mut trait clauses only)
    let mut base_substitutions: HashMap<String, PureExpr> = HashMap::new();
    insert_std_symbolic_substitutions(&mut base_substitutions, translated_args);

    // param_names override positional aliases (user's actual names take priority)
    if let Some(names) = param_names {
        for (idx, name) in names.iter().enumerate() {
            // Skip reserved names — "result" and "self" must not be overridden.
            if name == "result" || name == "self" {
                continue;
            }
            // User param names should be substituted regardless of fallback status.
            // Fallback args still have meaningful expressions (e.g., PureExpr::Var("arg0", None))
            // that can be substituted for the parameter name in the postcondition.
            if let Some(arg) = translated_args.get(idx) {
                base_substitutions.insert(name.clone(), arg.expr.clone());
            }
        }
    }

    // Reserved semantic bindings — highest priority, inserted last.
    base_substitutions.insert("result".to_string(), result_var.clone());

    // For method calls, args[0] is `self` (bound per clause).
    // Prefer non-fallback args, but accept fallback args as a last resort
    // so that postconditions using `self` are not silently dropped. A fallback
    // placeholder like `Var("arg0")` still produces a meaningful (if symbolic)
    // constraint rather than discarding the entire postcondition. (#1572)
    let self_arg_expr = explicit_self_expr
        .cloned()
        .or_else(|| translated_args.first().map(|arg| arg.expr.clone()));
    let stale_names = names_of_stale_arguments(translated_args, param_names);
    // Parse all ensures clauses once and store the parsed results. (#1935)
    // Previously, each clause was parsed twice: once for result extraction (pass 1)
    // and again for assumption recording (pass 2). This merges both passes to
    // share a single parse_contract call per clause.
    let parsed_clauses: Vec<_> = ensures
        .iter()
        .filter_map(|ensures_str| {
            let parsed = trust_wp_core::contract_parser::parse_contract(ensures_str)
                .map_err(|e| {
                    crate::result_protocol_state::record_parse_error();
                    format!("parse error: {e}")
                })
                .and_then(|expr| {
                    // The clause as the callee's own lane proves it, read at
                    // this call: the same state elaboration over the
                    // callee's signature, with its `old(..)` the call's
                    // pre-state.
                    postcondition_at_a_call(&expr, callee)
                        .map_err(|reason| format!("no reading at the call: {reason}"))
                })
                .and_then(|expr| match reads_a_stale_argument(&expr, &stale_names) {
                    Some(name) => Err(format!(
                        "no reading at the call: it reads `{name}`, whose argument is read \
                         through a reference after a store the argument's translation does not \
                         see, so it reads the pointee's entry value, not its value at the call"
                    )),
                    None => Ok(expr),
                });
            match parsed {
                Ok(ensures_expr) => {
                    // A clause that applies a parameter bound to an opaque
                    // callable (anything but an exact thunk value applied with
                    // no arguments) would have that application replaced by
                    // the closure's environment / an arity-shared UF. Drop it:
                    // an omitted postcondition only weakens the call's facts.
                    if let Some(name) = applied_opaque_callable_param(
                        &ensures_expr,
                        translated_args,
                        param_names,
                        self_arg_expr.is_some(),
                    ) {
                        debug!(
                            "trust-wp: postcondition `{ensures_str}` dropped: it applies \
                             `{name}`, which is bound to an opaque callable argument"
                        );
                        return None;
                    }
                    let substitutions = substitutions_for_expr(
                        ensures_str,
                        &ensures_expr,
                        &base_substitutions,
                        self_arg_expr.as_ref(),
                    );
                    Some((ensures_str, ensures_expr, substitutions))
                }
                Err(reason) => {
                    debug!(
                        "trust-wp: error: failed to read ensures clause `{ensures_str}`: {reason} \
                         (verification will fail — fail-closed #1739)"
                    );
                    effects.record_dropped_clause(
                        DroppedClauseKind::Postcondition,
                        ensures_str.clone(),
                        reason,
                    );
                    None
                }
            }
        })
        .collect();

    // Pass 1: extract a direct result constraint.
    // The first clause matching `result == <expr>` or `result@ == <expr>` wins.
    let mut extracted_result: Option<PureExpr> = None;
    for (ensures_str, ensures_expr, substitutions) in &parsed_clauses {
        if let Some(substituted) = try_extract_result_expr(
            ensures_expr,
            substitutions,
            param_names,
            ensures_str,
            match_view_result,
        ) {
            extracted_result = Some(substituted);
            break;
        }
    }

    // Pass 2: record ALL ensures clauses as assumptions.
    //
    // When a direct result constraint was extracted above, the remaining clauses
    // (those that did NOT match `result == <expr>`) still carry important
    // postconditions (mutation effects, overflow flags, clamping behavior, etc.).
    // These must be recorded as call-site assumptions so the solver can use them.
    //
    // ALL clauses (including the extracted one) are pushed as assumptions:
    // the extracted clause provides a ground binding that ay needs as a trigger
    // for e-matching quantified axioms. (#1581)
    //
    // When record_assumptions is false (substitution extraction pass), we skip
    // recording to avoid double-pushing (#1310).
    for (ensures_str, ensures_expr, substitutions) in &parsed_clauses {
        let unresolved = unresolved_symbolic_names(ensures_expr, substitutions, param_names);
        if unresolved.is_empty() {
            if record_assumptions {
                let substituted = connect_final_receiver_state_witness(
                    ensures_expr.substitute(substitutions),
                    self_arg_expr.as_ref(),
                );
                effects.assumptions.push(substituted.clone());

                // Eagerly add the FnOnce weakening of postcondition_mut:
                // postcondition_mut(self, args..., res_state, result)
                //   ==> postcondition_once(self, args..., result).
                //
                // The ay encoder has a quantified forward law, but adding
                // this ground call-site fact improves instantiation for
                // sequential FnMut calls where `resolve(...)` witnesses are
                // required by specs such as call_fnmut in Creusot's
                // mutable-capture suite (#970).
                if let PureExpr::MethodCall {
                    receiver,
                    method,
                    args,
                } = &substituted
                {
                    if method == "postcondition_mut" && args.len() >= 2 {
                        let mut once_args = args.clone();
                        once_args.remove(once_args.len() - 2); // drop res_state
                        effects.assumptions.push(PureExpr::MethodCall {
                            receiver: receiver.clone(),
                            method: "postcondition_once".to_string(),
                            args: once_args,
                        });
                    }
                }
            }
        } else {
            warn_unresolved_names(ensures_str, &unresolved, "postcondition");
            let names: Vec<&str> = unresolved.iter().map(String::as_str).collect();
            effects.record_dropped_clause(
                DroppedClauseKind::Postcondition,
                (*ensures_str).clone(),
                format!("unresolved symbolic names: {}", names.join(", ")),
            );
        }
    }

    // Return extracted result or unconstrained variable
    extracted_result.unwrap_or_else(|| result_var.clone())
}
