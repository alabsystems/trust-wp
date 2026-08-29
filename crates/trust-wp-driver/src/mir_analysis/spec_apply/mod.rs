// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract specification application at call sites.
//!
//! Handles parsing, substitution, and application of pre/postcondition
//! specifications when a function call is encountered during MIR extraction.
//! This module operates on `PureExpr` and spec strings — it does not depend
//! on rustc MIR types.

mod expr_traversal;
mod postcondition;
mod precondition;
mod receiver_state;
mod result_extraction;

use std::collections::{HashMap, HashSet};

use tracing::debug;
use trust_wp_core::formula::PureExpr;
#[cfg(test)]
use trust_wp_core::formula::{BinOp, MatchArm, Pattern};

#[cfg(test)]
use self::expr_traversal::replace_var_allow_bound;
// Re-export public API for consumers.
pub(super) use self::postcondition::{
    apply_postconditions_for_loop_body_with_effects, apply_postconditions_with_effects,
    apply_postconditions_with_self_and_effects,
};
pub(super) use self::precondition::{
    apply_preconditions_with_effects, apply_preconditions_with_self_and_effects,
    collect_precondition_obligations,
};
#[cfg(test)]
use crate::callbacks::final_receiver_state_expr;

/// A translated call argument expression with a fallback flag.
///
/// When an operand cannot be translated to a `PureExpr`, a fallback
/// placeholder (e.g., `Var("arg0")`) is used instead. The `is_fallback`
/// flag tracks this so that spec application can skip unresolvable
/// postconditions rather than producing incorrect substitutions.
#[derive(Clone, Debug)]
pub(super) struct TranslatedArg {
    pub(super) expr: PureExpr,
    pub(super) is_fallback: bool,
}

impl TranslatedArg {
    pub(super) fn new(expr: PureExpr) -> Self {
        Self {
            expr,
            is_fallback: false,
        }
    }

    pub(super) fn fallback(expr: PureExpr) -> Self {
        Self {
            expr,
            is_fallback: true,
        }
    }
}

/// Insert default symbolic substitutions used by std specs.
///
/// - `arg0`, `arg1`, ... always map to argument positions (including fallback
///   placeholders like `Var("arg1")` when translation fails).
/// - `value/default/arg/rhs` map to the first non-`self` argument:
///   `args[1]` for method calls, otherwise `args[0]` for associated functions.
fn insert_std_symbolic_substitutions(
    base_substitutions: &mut HashMap<String, PureExpr>,
    translated_args: &[TranslatedArg],
) {
    for (idx, arg) in translated_args.iter().enumerate() {
        // Keep positional aliases even for fallback placeholders so clauses that
        // reference `argN` can still be applied instead of being dropped.
        base_substitutions.insert(format!("arg{idx}"), arg.expr.clone());
    }

    // Always prefer the first non-self slot by position (args[1]) even when
    // it is a fallback placeholder. Falling back to args[0] (`self`) changes
    // call semantics for zero-arg Fn/FnMut/FnOnce specs. (#970)
    let value_arg = translated_args.get(1).or_else(|| translated_args.first());

    if let Some(arg) = value_arg {
        base_substitutions.insert("value".to_string(), arg.expr.clone());
        base_substitutions.insert("default".to_string(), arg.expr.clone());
        base_substitutions.insert("arg".to_string(), arg.expr.clone());
        base_substitutions.insert("rhs".to_string(), arg.expr.clone());
    }
}

/// Collect unresolved symbolic names from an expression.
///
/// Returns the set of known symbolic names (`self`, `value`, `default`,
/// `result`, `arg`, `rhs`, indexed aliases like `arg0`, plus any `param_names`)
/// that appear as free variables in the expression but
/// are NOT present in the substitution map. Used to decide whether a
/// postcondition can be safely applied.
fn unresolved_symbolic_names(
    expr: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    param_names: Option<&[String]>,
) -> HashSet<String> {
    let mut vars = expr.free_vars();
    vars.retain(|name| {
        let is_arg_indexed = name
            .strip_prefix("arg")
            .is_some_and(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()));
        let is_symbolic = matches!(
            name.as_str(),
            "self" | "value" | "default" | "result" | "arg" | "rhs"
        ) || param_names
            .is_some_and(|names| names.iter().any(|param_name| param_name == name))
            || is_arg_indexed;
        is_symbolic && !substitutions.contains_key(name)
    });
    vars
}

/// Print diagnostic for unresolved names without counting as a dropped clause.
///
/// Used in the first-pass `result == <expr>` extraction where the clause may
/// still be applied as a predicate assumption in the second pass.
fn warn_unresolved_names(clause: &str, unresolved: &HashSet<String>, kind: &str) {
    if unresolved.is_empty() {
        return;
    }
    let mut names: Vec<&str> = unresolved.iter().map(String::as_str).collect();
    names.sort_unstable();
    debug!(
        "trust-wp: warning: {kind} dropped due to unresolved symbolic names \
         [{}] in clause `{}`",
        names.join(", "),
        clause
    );
}

fn substitutions_for_expr(
    _clause: &str,
    _expr: &PureExpr,
    base_substitutions: &HashMap<String, PureExpr>,
    self_expr: Option<&PureExpr>,
) -> HashMap<String, PureExpr> {
    let mut substitutions = base_substitutions.clone();
    if let Some(self_expr) = self_expr {
        // Bind `self` to the reference directly for all clauses, including
        // deref_mut. The extra Deref wrapping that was here previously (#2578)
        // created a term mismatch between call-site assumptions and user
        // postconditions for DerefMut specs.
        substitutions.insert("self".to_string(), self_expr.clone());
    }
    substitutions
}

#[cfg(test)]
mod tests;
