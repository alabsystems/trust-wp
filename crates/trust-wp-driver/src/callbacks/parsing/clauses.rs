// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    contract_parser::{parse_contract, parse_contract_spanned},
    formula::{BinOp, PureExpr},
};

use crate::{
    contracts::FunctionContract,
    logic::{identity::ClausePosition, spec_calls::ClauseRef},
};

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

    /// Rewrite the clauses that are read inside the body (loop invariants and
    /// variants), leaving `requires` and `ensures` untouched.
    pub(super) fn rewrite_body_level_exprs(&mut self, substitutions: &HashMap<String, PureExpr>) {
        if substitutions.is_empty() {
            return;
        }
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

pub(super) fn parse_clause_inputs(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    report_errors: bool,
) -> Option<ParsedClauseInputs> {
    // Each clause is resolved in the contract owner's scope as it is parsed,
    // against the type-check body of the clause it is: its `trust-wp:`
    // marker kind and text (`logic::spec_calls`). A `requires`/`ensures`
    // stands at the top of the body, a loop clause somewhere inside it, after
    // locals its text cannot place.
    let resolved = |expr: PureExpr, kind: &str, text: &str| {
        let position = if matches!(kind, "requires" | "ensures") {
            ClausePosition::Signature
        } else {
            ClausePosition::Body
        };
        crate::logic::identity::resolve_logic_fn_paths_in_scope(
            tcx,
            contract.def_id,
            &expr,
            position,
            &ClauseRef::written(kind, text),
        )
    };
    let boolean = |clauses: &[String], label: &str, kind: &str| -> Vec<PureExpr> {
        clauses
            .iter()
            .filter_map(|clause| {
                parse_boolean_clause(clause, label, report_errors)
                    .map(|expr| resolved(expr, kind, clause))
            })
            .collect()
    };
    let variant = |clauses: &[String], label: &str| -> Vec<PureExpr> {
        clauses
            .iter()
            .filter_map(|clause| {
                parse_variant_clause(clause, label, report_errors)
                    .map(|expr| resolved(expr, "variant", clause))
            })
            .collect()
    };

    let requires = boolean(&contract.requires, "requires", "requires");
    let ensures = boolean(&contract.ensures, "ensures", "ensures");
    let invariants = boolean(&contract.invariants, "invariant", "invariant");

    let per_loop_invariants: Vec<(u32, u32, Vec<PureExpr>)> = contract
        .per_loop_invariants
        .iter()
        .map(|(start, end, invariants)| {
            (
                *start,
                *end,
                boolean(invariants, "per-loop invariant", "invariant"),
            )
        })
        .filter(|(_, _, invariants)| !invariants.is_empty())
        .collect();

    let per_loop_variants: Vec<(u32, u32, Vec<PureExpr>)> = contract
        .per_loop_variants
        .iter()
        .map(|(start, end, variants)| (*start, *end, variant(variants, "per-loop variant")))
        .filter(|(_, _, variants)| !variants.is_empty())
        .collect();

    let variants = variant(&contract.variants, "variant");

    let mut parsed = ParsedClauseInputs {
        requires,
        ensures,
        invariants,
        per_loop_invariants,
        per_loop_variants,
        variants,
    };

    // Read each raw-pointer cast at its operand's type in the same owner, after the
    // per-clause resolution above.
    parsed.rewrite_each_expr(|expr| {
        crate::logic::ptr_casts::classify_pointer_casts(tcx, contract.def_id, expr)
    });

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
        // `is_refused_as_boolean_clause` is trust-wp-core's, deliberately NOT a
        // local copy: `trust-wp-macros`' `spec_tc::driver_parses` skips its
        // rustc type-check for exactly the clauses refused here, so the two
        // must be one predicate. See its doc comment.
        // A closure postcondition names the returned value: one parameter.
        // With any other count no parameter is the returned value.
        Ok(PureExpr::Closure { params, .. }) if clause_kind == "ensures" && params.len() != 1 => {
            emit_clause_parse_error(
                report_errors,
                clause_kind,
                clause,
                "a closure postcondition takes exactly one parameter, the returned value",
            );
            None
        }
        Ok(expr) if expr.is_refused_as_boolean_clause() => {
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
