// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constructor equality pattern detection in quantifier bodies.
//!
//! Detects patterns like `scrutinee == Constructor(vars...)` and
//! `scrutinee == Outer(Inner(vars...))` for quantifier elimination.
//! Handles single-variable, multi-variable, and nested constructor patterns.
//!
//! Extracted from `quantifier_ctor_elim.rs` as part of #1988 structural decomposition.

use std::collections::HashSet;

use tracing::debug;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{
    super::{quantifier::QuantifierKind, AYEncoder},
    ConstructorEqInfo, InnerConstructorEq,
};

/// Check if a quantifier body has a constructor equality pattern that can be
/// eliminated using datatype tester/selector operations (#1752, #1765).
///
/// Detects patterns for one or more bound variables:
///
/// **Single-var:** `scrutinee == Constructor(v)` → elimination with one selector
/// **Multi-var:** `scrutinee == Pair(k, v)` → elimination with per-field selectors
///
/// Also handles reversed equality, `Deref(Var(...))` scrutinee, and nullary constructors.
///
/// `qvars` is the set of all quantifier-bound variable names. Detection succeeds
/// only when every constructor argument is a distinct quantifier variable.
///
/// For `Forall` quantifiers, the body MUST be shaped as `guard ==> consequent`
/// for the elimination to fire. A non-Implies body like `forall<v> x == Ctor(v)`
/// cannot be correctly eliminated to just `is_ctor(x)` — that would silently
/// weaken the formula (#1781). Other non-Implies forms (for example
/// `forall<v> x == Ctor(v) && P(v)`) are valid formulas but intentionally
/// left to the normal quantifier encoder to preserve semantics.
pub(crate) fn detect_constructor_eq<'a>(
    encoder: &AYEncoder,
    kind: QuantifierKind,
    body: &'a PureExpr,
    qvars: &[&str],
) -> Option<ConstructorEqInfo<'a>> {
    // For forall: body is `guard ==> consequent`, check guard.
    // For exists: body is the entire equality.
    // For forall with non-Implies body, the elimination cannot fire (#1781):
    // `forall<v> x == Ctor(v)` means "for all v, x equals Ctor(v)" which is NOT
    // equivalent to `is_ctor(x)`. Likewise, `forall<v> x == Ctor(v) && P(v)` is
    // not representable as just tester/selector substitution without additional
    // normalization. Returning None falls through to normal quantifier encoding.
    let eq_expr = match body {
        PureExpr::BinOp(lhs, BinOp::Implies, _) => lhs.as_ref(),
        _ if kind == QuantifierKind::Forall => return None,
        _ => body,
    };

    // Build a HashSet once for O(1) qvar membership tests, replacing the
    // O(Q) linear scan per constructor argument in extract_ctor_var_side
    // and extract_nested_ctor_var_side. (#2346)
    let qvar_set: HashSet<&str> = qvars.iter().copied().collect();

    // Check for equality: scrutinee == Constructor(vars...) or Constructor(vars...) == scrutinee
    // Also handles nested constructors like OwnResult::Ok(Some(t)). (#1296)
    let (scrutinee, ctor_name, var_field_map, inner_ctor) = match eq_expr {
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            if let Some(info) = extract_ctor_var_side(encoder, right, &qvar_set) {
                (left.as_ref(), info.0, info.1, None)
            } else if let Some(info) = extract_ctor_var_side(encoder, left, &qvar_set) {
                (right.as_ref(), info.0, info.1, None)
            } else if let Some((outer, inner)) =
                extract_nested_ctor_var_side(encoder, right, &qvar_set)
            {
                (left.as_ref(), outer.0, outer.1, Some(inner))
            } else if let Some((outer, inner)) =
                extract_nested_ctor_var_side(encoder, left, &qvar_set)
            {
                (right.as_ref(), outer.0, outer.1, Some(inner))
            } else {
                return None;
            }
        }
        _ => return None,
    };

    // Check that the constructor's datatype is declared
    let dt = encoder.constructor_datatype(ctor_name)?;

    Some(ConstructorEqInfo {
        scrutinee,
        ctor_name,
        datatype: dt,
        var_field_map,
        inner_ctor,
    })
}

/// Extract the base variable name from an expression, stripping wrapper nodes.
///
/// Handles `Var("x")`, `Deref(Var("x"))`, `Old(Var("x"))`, `Final(Var("x"))`,
/// `View(Var("x"))`, and arbitrarily nested combinations thereof. Returns
/// `None` for non-variable expressions like `Int(42)` or `BinOp(...)`.
///
/// This enables constructor equality detection for reference-typed quantifier
/// variables where the parser produces `Deref(Var("t"))` for `*t`. (#1296)
fn extract_base_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => extract_base_var_name(inner),
        _ => None,
    }
}

/// Extract constructor name and variable-to-field mappings from one side of an equality.
///
/// Matches constructors where ALL arguments are distinct quantifier variables from `qvar_set`.
/// Returns `None` if any constructor argument is not a quantifier variable or is duplicated.
///
/// Constructor arguments may be wrapped in `Deref`, `Old`, `Final`, or `View`
/// nodes (e.g., `OwnResult::Ok(*t)` where `*t` = `Deref(Var("t"))`). These
/// wrappers are stripped to extract the base variable name. (#1296)
///
/// Uses `HashSet<&str>` for O(1) qvar membership tests instead of the previous
/// O(Q) linear scan on `&[&str]`. (#2346)
fn extract_ctor_var_side<'a>(
    encoder: &AYEncoder,
    expr: &'a PureExpr,
    qvar_set: &HashSet<&str>,
) -> Option<(&'a str, Vec<(&'a str, usize)>)> {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            if args.is_empty() {
                if encoder.nullary_constructor_datatype(name).is_some() {
                    return Some((name.as_str(), Vec::new()));
                }
                return None;
            }
            let mut var_field_map = Vec::with_capacity(args.len());
            let mut seen_vars = HashSet::new();
            for (idx, arg) in args.iter().enumerate() {
                // Use extract_base_var_name to handle Deref(Var("t")),
                // Old(Var("t")), Final(Var("t")), View(Var("t")) in addition
                // to plain Var("t"). This enables constructor equality
                // elimination for reference-typed quantifier variables like
                // `forall<t: &T> *self == OwnResult::Ok(*t) ==> P(t)`,
                // where `*t` is parsed as Deref(Var("t")). (#1296)
                if let Some(base_name) = extract_base_var_name(arg) {
                    if qvar_set.contains(base_name) && seen_vars.insert(base_name) {
                        var_field_map.push((base_name, idx));
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
            }
            if var_field_map.is_empty() {
                None
            } else {
                Some((name.as_str(), var_field_map))
            }
        }
        PureExpr::Var(name, _) if encoder.nullary_constructor_datatype(name).is_some() => {
            Some((name.as_str(), Vec::new()))
        }
        _ => None,
    }
}

/// Extract a nested constructor pattern like `OwnResult::Ok(Some(t))` from
/// one side of an equality.
///
/// Returns `Some((outer_info, inner_info))` when the expression is a constructor
/// call with exactly one argument that is itself a constructor call whose
/// arguments are all distinct quantifier variables. Both constructors must have
/// registered datatypes.
///
/// This enables two-level constructor equality elimination for patterns like
/// `forall t. self == OwnResult::Ok(Some(t)) ==> P(t)`, which would otherwise
/// require E-matching chains that ay-dpll cannot handle in a single round.
/// (#1296)
#[allow(clippy::type_complexity)] // Nested tuple captures constructor analysis results
fn extract_nested_ctor_var_side<'a>(
    encoder: &AYEncoder,
    expr: &'a PureExpr,
    qvar_set: &HashSet<&str>,
) -> Option<((&'a str, Vec<(&'a str, usize)>), InnerConstructorEq<'a>)> {
    let PureExpr::LogicFnCall {
        name: outer_name,
        args: outer_args,
    } = expr
    else {
        return None;
    };

    debug!(
        "  [nested-ctor-detect] outer={outer_name} n_args={} inner={:?}",
        outer_args.len(),
        outer_args
            .first()
            .map(|a| format!("{a:?}").chars().take(80).collect::<String>()),
    );

    // Outer constructor must have exactly one arg that is NOT a qvar (it's a
    // nested constructor). Multi-field outer constructors with nested args
    // are not handled — too complex for this targeted optimization.
    if outer_args.len() != 1 {
        return None;
    }
    // The single arg must be a constructor call (possibly nullary).
    let inner_arg = &outer_args[0];
    match inner_arg {
        PureExpr::LogicFnCall {
            name: inner_name,
            args: inner_args,
        } => {
            // Check inner constructor has a registered datatype.
            let inner_dt = encoder.constructor_datatype(inner_name)?;
            // Check outer constructor has a registered datatype.
            let _outer_dt = encoder.constructor_datatype(outer_name)?;
            // Inner args must all be distinct qvars (or wrapped qvar
            // references like Deref(Var("t"))). (#1296)
            let mut var_field_map = Vec::with_capacity(inner_args.len());
            let mut seen_vars = HashSet::new();
            for (idx, arg) in inner_args.iter().enumerate() {
                if let Some(base_name) = extract_base_var_name(arg) {
                    if qvar_set.contains(base_name) && seen_vars.insert(base_name) {
                        var_field_map.push((base_name, idx));
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
            }
            if var_field_map.is_empty() && !inner_args.is_empty() {
                return None;
            }
            let inner = InnerConstructorEq {
                ctor_name: inner_name.as_str(),
                datatype: inner_dt,
                outer_field_index: 0,
                var_field_map,
            };
            // Outer constructor has no qvar-mapped fields (its single arg is the
            // inner constructor, not a qvar).
            Some(((outer_name.as_str(), Vec::new()), inner))
        }
        PureExpr::Var(inner_name, _)
            if encoder.nullary_constructor_datatype(inner_name).is_some() =>
        {
            // Inner is a nullary constructor like None.
            let inner_dt = encoder.constructor_datatype(inner_name)?;
            let _outer_dt = encoder.constructor_datatype(outer_name)?;
            let inner = InnerConstructorEq {
                ctor_name: inner_name.as_str(),
                datatype: inner_dt,
                outer_field_index: 0,
                var_field_map: Vec::new(),
            };
            Some(((outer_name.as_str(), Vec::new()), inner))
        }
        _ => None,
    }
}
