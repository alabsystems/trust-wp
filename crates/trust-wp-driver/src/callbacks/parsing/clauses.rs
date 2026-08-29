// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    contract_parser::{parse_contract, parse_contract_spanned},
    formula::{BinOp, PureExpr, UnOp},
};

use crate::contracts::FunctionContract;

/// Error from parsing textual contract clauses into `PureExpr` values.
#[derive(Debug, Clone, thiserror::Error)]
#[error("failed to parse {clause_kind} '{clause}' in {context}: {reason}")]
pub(in crate::callbacks) struct ClauseParseError {
    pub(in crate::callbacks) clause_kind: String,
    pub(in crate::callbacks) clause: String,
    pub(in crate::callbacks) context: String,
    pub(in crate::callbacks) reason: String,
}

pub(super) struct ParsedClauseInputs {
    pub(super) requires: Vec<PureExpr>,
    pub(super) ensures: Vec<PureExpr>,
    pub(super) invariants: Vec<PureExpr>,
    pub(super) per_loop_invariants: Vec<(u32, u32, Vec<PureExpr>)>,
    pub(super) per_loop_variants: Vec<(u32, u32, Vec<PureExpr>)>,
    pub(super) variants: Vec<PureExpr>,
}

impl ParsedClauseInputs {
    pub(super) fn rewrite_each_expr(&mut self, mut f: impl FnMut(&PureExpr) -> PureExpr) {
        for expr in &mut self.requires {
            *expr = f(expr);
        }
        for expr in &mut self.ensures {
            *expr = f(expr);
        }
        for expr in &mut self.invariants {
            *expr = f(expr);
        }
        for (_, _, invariants) in &mut self.per_loop_invariants {
            for expr in invariants {
                *expr = f(expr);
            }
        }
        for (_, _, variants) in &mut self.per_loop_variants {
            for expr in variants {
                *expr = f(expr);
            }
        }
        for expr in &mut self.variants {
            *expr = f(expr);
        }
    }

    pub(super) fn rewrite_all_exprs(&mut self, substitutions: &HashMap<String, PureExpr>) {
        if substitutions.is_empty() {
            return;
        }

        rewrite_expr_list(&mut self.requires, substitutions);
        rewrite_expr_list(&mut self.ensures, substitutions);
        rewrite_expr_list(&mut self.invariants, substitutions);
        rewrite_nested_expr_lists(&mut self.per_loop_invariants, substitutions);
        rewrite_nested_expr_lists(&mut self.per_loop_variants, substitutions);
        rewrite_expr_list(&mut self.variants, substitutions);
    }

    pub(super) fn has_explicit_clauses(&self) -> bool {
        !self.requires.is_empty()
            || !self.ensures.is_empty()
            || !self.invariants.is_empty()
            || !self.variants.is_empty()
    }

    pub(super) fn needs_loop_analysis(&self) -> bool {
        !self.invariants.is_empty() || !self.variants.is_empty()
    }
}

/// Check if a top-level expression is structurally guaranteed to be non-boolean.
///
/// Used to reject malformed contract clauses where `parse_contract` succeeds
/// but the result cannot be a boolean predicate. For example, a char literal
/// `'a'` parses as `Int(97)` after #1513, but a bare integer is never a valid
/// requires/ensures/invariant clause.
///
/// Conservative: returns `true` only when the expression is DEFINITELY not
/// boolean. Returns `false` for ambiguous cases (variables, method calls, etc.)
/// to avoid false rejections.
fn is_definitely_non_boolean(expr: &PureExpr) -> bool {
    match expr {
        // Bare integer literals are never boolean predicates
        PureExpr::Int(_) => true,
        // Arithmetic and bitwise operators produce integers
        PureExpr::BinOp(
            _,
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::BitAnd
            | BinOp::BitXor
            | BinOp::BitOr,
            _,
        ) => true,
        // Negation (unary minus) produces an integer
        PureExpr::UnOp(UnOp::Neg, _) => true,
        // Wrappers inherit from inner expression
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            is_definitely_non_boolean(inner)
        }
        // Everything else is ambiguous — don't reject
        _ => false,
    }
}

pub(super) fn parse_clause_inputs(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    report_errors: bool,
) -> Option<ParsedClauseInputs> {
    let requires: Vec<_> = contract
        .requires
        .iter()
        .filter_map(|clause| parse_boolean_clause(clause, "requires", report_errors))
        .collect();

    let ensures: Vec<_> = contract
        .ensures
        .iter()
        .filter_map(|clause| parse_boolean_clause(clause, "ensures", report_errors))
        .collect();

    let invariants: Vec<_> = contract
        .invariants
        .iter()
        .filter_map(|clause| parse_boolean_clause(clause, "invariant", report_errors))
        .collect();

    let per_loop_invariants: Vec<(u32, u32, Vec<PureExpr>)> = contract
        .per_loop_invariants
        .iter()
        .map(|(start, end, invariants)| {
            let parsed: Vec<PureExpr> = invariants
                .iter()
                .filter_map(|clause| {
                    parse_boolean_clause(clause, "per-loop invariant", report_errors)
                })
                .collect();
            (*start, *end, parsed)
        })
        .filter(|(_, _, invariants)| !invariants.is_empty())
        .collect();

    let per_loop_variants: Vec<(u32, u32, Vec<PureExpr>)> = contract
        .per_loop_variants
        .iter()
        .map(|(start, end, variants)| {
            let parsed: Vec<PureExpr> = variants
                .iter()
                .filter_map(|clause| {
                    parse_variant_clause(clause, "per-loop variant", report_errors)
                })
                .collect();
            (*start, *end, parsed)
        })
        .filter(|(_, _, variants)| !variants.is_empty())
        .collect();

    let variants: Vec<_> = contract
        .variants
        .iter()
        .filter_map(|clause| parse_variant_clause(clause, "variant", report_errors))
        .collect();

    let parsed = ParsedClauseInputs {
        requires,
        ensures,
        invariants,
        per_loop_invariants,
        per_loop_variants,
        variants,
    };

    if has_dropped_clauses(tcx, contract, &parsed) {
        return None;
    }

    Some(parsed)
}

/// Parse textual contract clauses into `PureExpr` values.
///
/// Uses spanned parsing ([`parse_contract_spanned`]) so that parse errors
/// include byte-offset context from the contract string.
pub(in crate::callbacks) fn parse_contract_clauses(
    clauses: &[String],
    clause_kind: &str,
    context: &str,
) -> Result<Vec<PureExpr>, ClauseParseError> {
    clauses
        .iter()
        .map(|clause| {
            parse_contract_spanned(clause)
                .map(|spanned| spanned.into_expr())
                .map_err(|e| ClauseParseError {
                    clause_kind: clause_kind.to_string(),
                    clause: clause.clone(),
                    context: context.to_string(),
                    reason: e.to_string(),
                })
        })
        .collect()
}

/// Build a conjunction from a list of pure expressions.
///
/// Empty conjunction is `true`.
pub(in crate::callbacks) fn conjoin_exprs(exprs: &[PureExpr]) -> PureExpr {
    exprs
        .iter()
        .cloned()
        .reduce(|left, right| PureExpr::BinOp(Arc::new(left), BinOp::And, Arc::new(right)))
        .unwrap_or(PureExpr::Bool(true))
}

fn parse_boolean_clause(clause: &str, clause_kind: &str, report_errors: bool) -> Option<PureExpr> {
    match parse_contract(clause) {
        Ok(expr) if is_definitely_non_boolean(&expr) => {
            if report_errors {
                crate::result_protocol_state::record_parse_error();
            }
            eprintln!(
                "trust-wp: frontend diagnostic: failed to parse {clause_kind} '{clause}': \
                 expression is not a boolean predicate"
            );
            None
        }
        Ok(expr) => Some(expr),
        Err(error) => {
            emit_clause_parse_error(report_errors, clause_kind, clause, &error.to_string());
            None
        }
    }
}

fn parse_variant_clause(clause: &str, clause_kind: &str, report_errors: bool) -> Option<PureExpr> {
    match parse_contract(clause) {
        Ok(expr) => Some(expr),
        Err(error) => {
            emit_clause_parse_error(report_errors, clause_kind, clause, &error.to_string());
            None
        }
    }
}

fn emit_clause_parse_error(report_errors: bool, clause_kind: &str, clause: &str, error: &str) {
    if report_errors {
        crate::result_protocol_state::record_parse_error();
        eprintln!(
            "trust-wp: frontend diagnostic: failed to parse {clause_kind} '{clause}': {error}"
        );
    } else {
        eprintln!("trust-wp: warning: failed to parse {clause_kind} '{clause}': {error}");
    }
}

fn has_dropped_clauses(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    parsed: &ParsedClauseInputs,
) -> bool {
    let requires_dropped = parsed.requires.len() < contract.requires.len();
    let ensures_dropped = parsed.ensures.len() < contract.ensures.len();
    let invariants_dropped = parsed.invariants.len() < contract.invariants.len();
    let variants_dropped = parsed.variants.len() < contract.variants.len();

    let original_per_loop_count: usize = contract
        .per_loop_invariants
        .iter()
        .map(|(_, _, invariants)| invariants.len())
        .sum();
    let parsed_per_loop_count: usize = parsed
        .per_loop_invariants
        .iter()
        .map(|(_, _, invariants)| invariants.len())
        .sum();
    let per_loop_invariants_dropped = parsed_per_loop_count < original_per_loop_count;

    let original_per_loop_variant_count: usize = contract
        .per_loop_variants
        .iter()
        .map(|(_, _, variants)| variants.len())
        .sum();
    let parsed_per_loop_variant_count: usize = parsed
        .per_loop_variants
        .iter()
        .map(|(_, _, variants)| variants.len())
        .sum();
    let per_loop_variants_dropped = parsed_per_loop_variant_count < original_per_loop_variant_count;

    if !requires_dropped
        && !ensures_dropped
        && !invariants_dropped
        && !variants_dropped
        && !per_loop_invariants_dropped
        && !per_loop_variants_dropped
    {
        return false;
    }

    let mut dropped_kinds = Vec::new();
    if requires_dropped {
        dropped_kinds.push("requires");
    }
    if ensures_dropped {
        dropped_kinds.push("ensures");
    }
    if invariants_dropped || per_loop_invariants_dropped {
        dropped_kinds.push("invariant");
    }
    if variants_dropped {
        dropped_kinds.push("variant");
    }
    if per_loop_variants_dropped && !variants_dropped {
        dropped_kinds.push("per-loop variant");
    }

    let def_path = tcx.def_path_str(contract.def_id);
    eprintln!(
        "trust-wp: frontend diagnostic: function `{def_path}` has unparseable {} clause(s) \
         — skipping verification to prevent unsound results",
        dropped_kinds.join("/")
    );
    true
}

fn rewrite_expr_list(exprs: &mut [PureExpr], substitutions: &HashMap<String, PureExpr>) {
    for expr in exprs {
        *expr = expr.substitute(substitutions);
    }
}

fn rewrite_nested_expr_lists(
    exprs: &mut [(u32, u32, Vec<PureExpr>)],
    substitutions: &HashMap<String, PureExpr>,
) {
    for (_, _, nested_exprs) in exprs {
        rewrite_expr_list(nested_exprs, substitutions);
    }
}
