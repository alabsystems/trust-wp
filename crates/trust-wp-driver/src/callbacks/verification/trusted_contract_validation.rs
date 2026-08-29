// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fail-closed validation for trusted-function contracts.
//!
//! Trusted functions are skipped by the verifier, so their contracts must not
//! silently assume references that are invalid in program-function contracts.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{contract_parser::parse_contract_body, formula::PureExpr};

use super::super::super::contracts::FunctionContract;

pub(super) struct TrustedContractValidationError {
    pub(super) contract_def_id: DefId,
    pub(super) message: String,
}

#[derive(Debug)]
struct GhostFnName {
    full_path: String,
    relative_path: Option<String>,
    item_name: String,
}

/// Validate trusted function clauses before `#[trusted]` skip handling.
///
/// A trusted program function must not place calls to `#[check(ghost)]`
/// functions in its requires/ensures clauses. Without this guard, those clauses
/// are assumed without validating that the referenced ghost-only helper is
/// legal in the program contract context.
pub(super) fn validate_trusted_contract_references(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
) -> Vec<TrustedContractValidationError> {
    let ghost_names = collect_ghost_function_names(tcx, contracts);
    if ghost_names.is_empty() {
        return Vec::new();
    }

    let mut errors = Vec::new();
    for contract in contracts {
        if !contract.trusted || contract.ghost {
            continue;
        }

        for (kind, clause) in contract_clauses(contract) {
            let Ok(expr) = parse_contract_body(clause) else {
                continue;
            };
            if let Some(ghost_fn) = first_referenced_ghost_fn(&expr, &ghost_names) {
                let contract_path = tcx.def_path_str(contract.def_id);
                errors.push(TrustedContractValidationError {
                    contract_def_id: contract.def_id,
                    message: format!(
                        "trusted contract validation: `{contract_path}` {kind} clause calls \
                         ghost function `{ghost_fn}`. Trusted program-function contracts \
                         cannot reference #[check(ghost)] functions because their bodies are \
                         skipped and the ghost-only contract reference would be assumed."
                    ),
                });
            }
        }
    }

    errors
}

fn collect_ghost_function_names(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
) -> HashMap<String, GhostFnName> {
    let mut names = HashMap::new();
    for contract in contracts.iter().filter(|contract| contract.ghost) {
        let full_path = tcx.def_path_str(contract.def_id);
        let item_name = item_name_from_def_path(&full_path);
        let relative_path = full_path
            .split_once("::")
            .and_then(|(_, relative)| (!relative.is_empty()).then_some(relative.to_string()));
        let ghost_name = GhostFnName {
            full_path: full_path.clone(),
            relative_path,
            item_name: item_name.clone(),
        };
        names.insert(full_path, ghost_name);
    }
    names
}

fn item_name_from_def_path(full_path: &str) -> String {
    full_path
        .rsplit("::")
        .next()
        .unwrap_or(full_path)
        .to_string()
}

fn contract_clauses(contract: &FunctionContract) -> impl Iterator<Item = (&'static str, &str)> {
    contract
        .requires
        .iter()
        .map(|clause| ("requires", clause.as_str()))
        .chain(
            contract
                .ensures
                .iter()
                .map(|clause| ("ensures", clause.as_str())),
        )
        .chain(
            contract
                .invariants
                .iter()
                .map(|clause| ("invariant", clause.as_str())),
        )
        .chain(
            contract
                .variants
                .iter()
                .map(|clause| ("variant", clause.as_str())),
        )
}

fn first_referenced_ghost_fn(
    expr: &PureExpr,
    ghost_names: &HashMap<String, GhostFnName>,
) -> Option<String> {
    let mut referenced = None;
    let mut seen = HashSet::new();
    expr.for_each_recursive(|node| {
        if referenced.is_some() {
            return;
        }
        let PureExpr::LogicFnCall { name, .. } = node else {
            return;
        };
        if !seen.insert(name.clone()) {
            return;
        }
        referenced = ghost_names
            .values()
            .find(|ghost_name| logic_call_matches_ghost_fn(name, ghost_name))
            .map(|ghost_name| ghost_name.full_path.clone());
    });
    referenced
}

fn logic_call_matches_ghost_fn(call_name: &str, ghost_name: &GhostFnName) -> bool {
    call_name == ghost_name.full_path
        || ghost_name
            .relative_path
            .as_deref()
            .is_some_and(|relative| call_name == relative)
        || call_name == ghost_name.item_name
        || call_name
            .strip_prefix("crate::")
            .is_some_and(|stripped| ghost_name.relative_path.as_deref() == Some(stripped))
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use trust_wp_core::contract_parser::parse_contract_body;

    use super::{first_referenced_ghost_fn, item_name_from_def_path, GhostFnName};

    fn ghost_names() -> HashMap<String, GhostFnName> {
        HashMap::from([(
            "test_crate::specs::faux".to_string(),
            GhostFnName {
                full_path: "test_crate::specs::faux".to_string(),
                relative_path: Some("specs::faux".to_string()),
                item_name: "faux".to_string(),
            },
        )])
    }

    #[test]
    fn detects_unqualified_ghost_function_call_in_contract_clause() {
        let expr = parse_contract_body("faux()").expect("clause should parse");

        assert_eq!(
            first_referenced_ghost_fn(&expr, &ghost_names()).as_deref(),
            Some("test_crate::specs::faux"),
        );
    }

    #[test]
    fn ignores_nearby_non_call_variable_name() {
        let expr = parse_contract_body("faux == 0").expect("clause should parse");

        assert!(
            first_referenced_ghost_fn(&expr, &ghost_names()).is_none(),
            "a variable named like a ghost function is not a ghost function call"
        );
    }

    #[test]
    fn detects_relative_ghost_function_call_in_contract_clause() {
        let expr = parse_contract_body("specs::faux()").expect("clause should parse");

        assert_eq!(
            first_referenced_ghost_fn(&expr, &ghost_names()).as_deref(),
            Some("test_crate::specs::faux"),
        );
    }

    #[test]
    fn item_name_from_def_path_handles_named_function() {
        assert_eq!(item_name_from_def_path("test_crate::specs::faux"), "faux");
    }

    #[test]
    fn item_name_from_def_path_handles_closure_def_path() {
        assert_eq!(
            item_name_from_def_path("test_crate::foo::{closure#0}"),
            "{closure#0}"
        );
    }
}
