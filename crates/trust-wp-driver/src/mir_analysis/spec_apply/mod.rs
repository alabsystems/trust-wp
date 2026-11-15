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
    apply_invariant_preconditions_with_effects, apply_preconditions_with_effects,
    apply_preconditions_with_self_and_effects, collect_precondition_obligations,
};
#[cfg(test)]
use crate::callbacks::final_receiver_state_expr;

/// A translated call argument expression with a fallback flag.
///
/// When an operand cannot be translated to a `PureExpr`, a fallback
/// placeholder (e.g., `Var("arg0")`) is used instead. The `is_fallback`
/// flag tracks this so that spec application can skip unresolvable
/// postconditions rather than producing incorrect substitutions.
///
/// `exact_callable_value` is set ONLY by the exact-thunk rule
/// (`closure::resolve_closed_thunk_closure_args`): the argument is a
/// capture-free, parameter-free closure whose MIR body provably returns
/// exactly `expr`. Every other argument is an *opaque callable* for the
/// purpose of contract application: a clause that APPLIES the parameter bound
/// to it (`f()`, `f(x)`, any arity) never has that application replaced by the
/// argument's expression — see [`applied_opaque_callable_param`].
#[derive(Clone, Debug)]
pub(super) struct TranslatedArg {
    pub(super) expr: PureExpr,
    pub(super) is_fallback: bool,
    pub(super) exact_callable_value: bool,
    /// The argument reads a pointee after a store through it (or an alias)
    /// that its translation does not see (`deref_store_staleness`): `expr`
    /// reads the pointee's ENTRY value, not its value at the call. A callee
    /// clause is a fact about the call's pre-state, so a clause that reads
    /// such an argument there (anything but its prophecy `^p`) has no reading
    /// at this call.
    pub(super) stale: bool,
}

impl TranslatedArg {
    pub(super) fn new(expr: PureExpr) -> Self {
        Self {
            expr,
            is_fallback: false,
            exact_callable_value: false,
            stale: false,
        }
    }

    pub(super) fn fallback(expr: PureExpr) -> Self {
        Self {
            expr,
            is_fallback: true,
            exact_callable_value: false,
            stale: false,
        }
    }

    /// A zero-argument callable whose every call returns exactly `value`.
    ///
    /// Only the exact-thunk body-shape rule may construct this.
    pub(super) fn exact_thunk_value(value: PureExpr) -> Self {
        Self {
            expr: value,
            is_fallback: false,
            exact_callable_value: true,
            stale: false,
        }
    }

    /// True unless this argument is an exact thunk value.
    pub(super) fn opaque_callable(&self) -> bool {
        !self.exact_callable_value
    }
}

/// Return the name of a parameter that `clause` APPLIES (as `name(..)`, any
/// arity) when that application cannot be replaced by a value exactly.
///
/// The contract substitution (`PureExpr::substitute`) replaces a zero-argument
/// application `f()` by the expression bound to `f`, and leaves `f(x)` as an
/// uninterpreted function symbol `f` shared by every call site. Both are only
/// faithful when the bound argument is an exact thunk value applied with zero
/// arguments. Anything else — a capturing closure (whose expression is its
/// environment tuple), a closure with parameters, a fallback `argN`, a
/// function item, `self` — must not let the clause through.
pub(super) fn applied_opaque_callable_param(
    clause: &PureExpr,
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    has_self: bool,
) -> Option<String> {
    // name -> Some(arg index) for argument bindings, None for `self`.
    let mut bound: HashMap<String, Option<usize>> = HashMap::new();
    for idx in 0..translated_args.len() {
        bound.insert(format!("arg{idx}"), Some(idx));
    }
    if !translated_args.is_empty() {
        let value_idx = if translated_args.len() > 1 { 1 } else { 0 };
        for alias in VALUE_ALIASES {
            bound.insert(alias.to_string(), Some(value_idx));
        }
    }
    if let Some(names) = param_names {
        for (idx, name) in names.iter().enumerate() {
            if name == "result" || name == "self" {
                continue;
            }
            if idx < translated_args.len() {
                bound.insert(name.clone(), Some(idx));
            }
        }
    }
    if has_self || !translated_args.is_empty() {
        bound.insert("self".to_string(), None);
    }

    let mut found: Option<String> = None;
    clause.for_each_recursive(|node| {
        if found.is_some() {
            return;
        }
        let PureExpr::LogicFnCall { name, args } = node else {
            return;
        };
        let Some(binding) = bound.get(name) else {
            return;
        };
        let opaque = match binding {
            None => true,
            Some(_) if !args.is_empty() => true,
            Some(idx) => translated_args[*idx].opaque_callable(),
        };
        if opaque {
            found = Some(name.clone());
        }
    });
    found
}

/// The names besides `argN` a call binds to an argument by POSITION (the
/// first argument that is not `self`) rather than by the callee's parameter
/// names. A std spec's text spells its parameters so.
pub(super) const VALUE_ALIASES: [&str; 4] = ["value", "default", "arg", "rhs"];

/// Whether a call binds `name` to an argument by position: `argN` or one of
/// [`VALUE_ALIASES`]. A local contract that reads such a name free, with no
/// parameter of that name, means something else by it (a constant, a static,
/// a capture), and every call would read it as an argument; discovery refuses
/// that clause (`param_patterns::refuse_positional_alias_collisions`, D-179).
pub(crate) fn is_positional_alias(name: &str) -> bool {
    VALUE_ALIASES.contains(&name)
        || name
            .strip_prefix("arg")
            .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()))
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
        for alias in VALUE_ALIASES {
            base_substitutions.insert(alias.to_string(), arg.expr.clone());
        }
    }
}

/// `text`, parsed, when a call reads it as written: the state elaboration
/// every call reads a callee clause through
/// (`formula::elaborate::postcondition_at_a_call`) leaves it unchanged.
///
/// A lane that matches a callee clause's shape (`(^self)@ == e`, `result ==
/// e`, `^p == e`) and substitutes the arguments for the parameters reads the
/// text as written. A clause the elaboration reads otherwise has another
/// meaning at the call (a pre-Creusot `*p` is `^p`; a callee's `old(e)` is
/// `e` in the call's pre-state, not the caller's entry state) or none (a read
/// it refuses), so such a lane gets no reading of it: `None`.
pub(in crate::mir_analysis) fn clause_read_as_written(
    text: &str,
    callee: &trust_wp_core::formula::elaborate::Signature,
) -> Option<PureExpr> {
    let parsed = trust_wp_core::contract_parser::parse_contract(text).ok()?;
    let read = trust_wp_core::formula::elaborate::postcondition_at_a_call(&parsed, callee).ok()?;
    (read == parsed).then_some(parsed)
}

/// The names a clause reads argument `idx` by: its parameter name, `argN`,
/// `self` for the first and the value aliases (`value`, `default`, `arg`,
/// `rhs`) for the first argument that is not `self`, as
/// [`insert_std_symbolic_substitutions`] binds them. An explicit `self` is
/// derived from the first argument, so it is read as stale with it.
pub(in crate::mir_analysis) fn names_of_stale_arguments(
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
) -> HashSet<String> {
    let mut names = HashSet::new();
    let value_idx = if translated_args.len() > 1 { 1 } else { 0 };
    for (idx, arg) in translated_args.iter().enumerate() {
        if !arg.stale {
            continue;
        }
        names.insert(format!("arg{idx}"));
        if let Some(name) = param_names.and_then(|names| names.get(idx)) {
            names.insert(name.clone());
        }
        if idx == 0 {
            names.insert("self".to_string());
        }
        if idx == value_idx {
            names.extend(VALUE_ALIASES.map(String::from));
        }
    }
    names
}

/// The first name of `stale` that `clause` reads other than as the operand
/// of `^` (the prophecy a call argument carries is the call's own).
pub(in crate::mir_analysis) fn reads_a_stale_argument(
    clause: &PureExpr,
    stale: &HashSet<String>,
) -> Option<String> {
    if stale.is_empty() {
        return None;
    }
    let prophecies_removed = clause.rewrite_bottom_up(|node| match node {
        PureExpr::Final(ref inner)
            if matches!(inner.as_ref(), PureExpr::Var(name, _) if stale.contains(name)) =>
        {
            PureExpr::Bool(true)
        }
        node => node,
    });
    let mut read: Vec<String> = prophecies_removed
        .free_vars()
        .into_iter()
        .filter(|name| stale.contains(name))
        .collect();
    read.sort_unstable();
    read.into_iter().next()
}

/// Collect unresolved symbolic names from an expression.
///
/// Returns the set of known symbolic names (`self`, `value`, `default`,
/// `result`, `arg`, `rhs`, indexed aliases like `arg0`, plus any `param_names`)
/// that appear as free variables in the expression but
/// are NOT present in the substitution map. Used to decide whether a
/// postcondition can be safely applied.
pub(in crate::mir_analysis) fn unresolved_symbolic_names(
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
