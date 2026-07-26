// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT-LIB2 formula printer.
//!
//! Converts `Formula` AST nodes (including separation logic constructs)
//! to SMT-LIB2 text.

use std::fmt::Write;

use super::{context::SmtContext, expr_printer::write_expr_ctx, MAX_RECURSION_DEPTH};
use crate::formula::{Formula, Location, Permission, Value};

/// Convert a `Formula` to SMT-LIB2 format.
///
/// This includes separation-logic specific encodings for points-to assertions
/// and separating conjunction.
#[must_use]
pub fn formula_to_smt(formula: &Formula) -> String {
    let mut s = String::new();
    write_formula(&mut s, formula);
    s
}

/// Extract the footprint (heap location names) from a formula.
///
/// Used for generating disjointness constraints in separating conjunction.
/// Returns a list of unique location variable names from all `PointsTo` assertions.
#[cfg(test)]
pub(crate) fn extract_footprint_names(formula: &Formula) -> Vec<String> {
    let mut locs = Vec::new();
    collect_footprint_names(formula, &mut locs, 0);
    // Deduplicate while preserving order (for deterministic output)
    let mut seen = std::collections::HashSet::new();
    locs.into_iter()
        .filter(|loc| seen.insert(loc.clone()))
        .collect()
}

/// Recursively collect heap location names from a formula.
fn collect_footprint_names(formula: &Formula, locs: &mut Vec<String>, depth: usize) {
    if depth > MAX_RECURSION_DEPTH {
        return;
    }
    match formula {
        Formula::PointsTo { location, .. } => {
            locs.push(location.0.clone());
        }
        Formula::SepConj(l, r)
        | Formula::And(l, r)
        | Formula::Or(l, r)
        | Formula::Implies(l, r)
        | Formula::MagicWand(l, r) => {
            collect_footprint_names(l, locs, depth + 1);
            collect_footprint_names(r, locs, depth + 1);
        }
        Formula::Forall { body, triggers, .. } | Formula::Exists { body, triggers, .. } => {
            collect_footprint_names(body, locs, depth + 1);
            for pattern in triggers {
                for trigger in pattern {
                    collect_footprint_names(trigger, locs, depth + 1);
                }
            }
        }
        Formula::True | Formula::False | Formula::Pure(_) | Formula::MutBorrow { .. } => {
            // No heap footprint
        }
    }
}

fn write_points_to(out: &mut String, location: &Location, value: &Value, permission: Permission) {
    let loc = &location.0;
    let perm_value = permission.scaled_value();
    let _ = write!(
        out,
        "(and (select heap_domain {loc}) (>= (select heap_perms {loc}) {perm_value}) "
    );
    match value {
        Value::Expr(expr) => {
            let _ = write!(out, "(= (select heap_contents {loc}) ");
            write_expr_ctx(out, expr, SmtContext::Normal);
            out.push(')');
        }
        Value::Unknown => out.push_str("true"),
    }
    out.push(')');
}

fn write_sep_conj(out: &mut String, l: &Formula, r: &Formula, depth: usize) {
    let mut left_locs = Vec::new();
    collect_footprint_names(l, &mut left_locs, depth + 1);
    let mut right_locs = Vec::new();
    collect_footprint_names(r, &mut right_locs, depth + 1);

    if left_locs.is_empty() || right_locs.is_empty() {
        out.push_str("(and ");
        write_formula_depth(out, l, depth + 1);
        out.push(' ');
        write_formula_depth(out, r, depth + 1);
        out.push(')');
        return;
    }

    // Cross-pair disjointness: for each l ∈ footprint(P), r ∈ footprint(Q), assert l ≠ r.
    // O(L*R) but L and R are typically very small (1-3 locations per side).
    // NOTE: We must NOT use `distinct(all_locs)` — that would add intra-side
    // constraints, which is semantically incorrect for separating conjunction. See #449.
    out.push_str("(and ");
    write_formula_depth(out, l, depth + 1);
    out.push(' ');
    write_formula_depth(out, r, depth + 1);
    out.push(' ');

    let total_pairs = left_locs.len() * right_locs.len();
    if total_pairs > 1 {
        out.push_str("(and ");
    }
    let mut first = true;
    for ll in &left_locs {
        for rr in &right_locs {
            if !first {
                out.push(' ');
            }
            first = false;
            let _ = write!(out, "(not (= {ll} {rr}))");
        }
    }
    if total_pairs > 1 {
        out.push(')');
    }
    out.push(')');
}

/// Write a quantifier body with optional `:pattern` trigger annotations.
fn write_body_with_triggers(
    out: &mut String,
    body: &Formula,
    triggers: &[Vec<Formula>],
    depth: usize,
) {
    if triggers.is_empty() {
        write_formula_depth(out, body, depth);
    } else {
        out.push_str("(! ");
        write_formula_depth(out, body, depth);
        for pattern in triggers {
            out.push_str(" :pattern (");
            for (i, trigger) in pattern.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                write_formula_depth(out, trigger, depth);
            }
            out.push(')');
        }
        out.push(')');
    }
}

/// Core formula to SMT conversion — writes directly to a buffer (#506 F1).
pub(super) fn write_formula(out: &mut String, formula: &Formula) {
    write_formula_depth(out, formula, 0);
}

fn write_formula_depth(out: &mut String, formula: &Formula, depth: usize) {
    if depth > MAX_RECURSION_DEPTH {
        out.push_str("false");
        return;
    }
    match formula {
        Formula::True => out.push_str("true"),
        Formula::False => out.push_str("false"),
        Formula::Pure(expr) => write_expr_ctx(out, expr, SmtContext::Normal),
        Formula::And(left, right) => {
            out.push_str("(and ");
            write_formula_depth(out, left, depth + 1);
            out.push(' ');
            write_formula_depth(out, right, depth + 1);
            out.push(')');
        }
        Formula::Or(left, right) => {
            out.push_str("(or ");
            write_formula_depth(out, left, depth + 1);
            out.push(' ');
            write_formula_depth(out, right, depth + 1);
            out.push(')');
        }
        Formula::Implies(left, right) => {
            out.push_str("(=> ");
            write_formula_depth(out, left, depth + 1);
            out.push(' ');
            write_formula_depth(out, right, depth + 1);
            out.push(')');
        }
        Formula::Forall {
            var,
            body,
            triggers,
            ..
        } => {
            let _ = write!(out, "(forall (({var} Int)) ");
            write_body_with_triggers(out, body, triggers, depth + 1);
            out.push(')');
        }
        Formula::Exists {
            var,
            body,
            triggers,
            ..
        } => {
            let _ = write!(out, "(exists (({var} Int)) ");
            write_body_with_triggers(out, body, triggers, depth + 1);
            out.push(')');
        }
        Formula::PointsTo {
            location,
            value,
            permission,
        } => write_points_to(out, location, value, *permission),
        Formula::MutBorrow {
            var,
            current,
            final_val,
            id,
        } => {
            let _ = write!(out, "(and (= {var}_current ");
            write_expr_ctx(out, current, SmtContext::Normal);
            let _ = write!(out, ") (= {var}_final ");
            write_expr_ctx(out, final_val, SmtContext::Normal);
            let _ = write!(out, ") (= {var}_id ");
            write_expr_ctx(out, id, SmtContext::Normal);
            out.push_str("))");
        }
        Formula::SepConj(l, r) => write_sep_conj(out, l, r, depth),
        Formula::MagicWand(ante, conseq) => {
            out.push_str("(=> ");
            write_formula_depth(out, ante, depth + 1);
            out.push(' ');
            write_formula_depth(out, conseq, depth + 1);
            out.push(')');
        }
    }
}
