// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trusted `proof_assert!` assumption collection.
//!
//! Iterates over contracts, detects proof_asserts via MIR, and collects
//! trusted trailing expressions and leading lemma-call postconditions.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
use tracing::{debug, warn};
use trust_wp_core::{contract_parser::parse_contract_body, formula::PureExpr, logic::LogicFnDef};
use trust_wp_driver::StdSpec;

use super::super::{
    proof_assert_leading_calls::collect_leading_proof_assert_assumptions, try_get_body_with_context,
};
use crate::{
    callbacks::logic_fn_scope::build_logic_fn_path_map, contracts::FunctionContract,
    mir_analysis::get_mir_body, proof_assert::find_proof_asserts_in_mir,
};

/// Collect trusted proof_assert assumptions using MIR-based detection.
///
/// Iterates over all contracts, detects proof_asserts in each function's MIR
/// body via `find_proof_asserts_in_mir`, and collects:
/// - trusted proof_assert trailing expressions
/// - leading lemma-call postconditions from any proof_assert body
///
/// Phase 5 (#1572): Migrated from HIR-based `proof_asserts` parameter to
/// MIR-based per-function detection. Path conditions are now implicit in
/// the MIR CFG, so the path condition parsing loop is removed.
/// Returns `(assumptions_by_fn, warning_count)` where `warning_count` is
/// the number of trusted proof_assert expressions that failed to parse
/// and were dropped.
pub(in crate::callbacks) fn collect_trusted_proof_assert_assumptions(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    user_specs: &HashMap<DefId, StdSpec>,
    logic_fn_defs: &[LogicFnDef],
) -> (HashMap<LocalDefId, Vec<PureExpr>>, usize) {
    let mut assumptions_by_fn: HashMap<LocalDefId, Vec<PureExpr>> = HashMap::new();
    let mut warning_count = 0usize;

    for contract in contracts {
        let Some(body_with_facts) = try_get_body_with_context(contract.local_def_id) else {
            continue;
        };
        let mir_body = get_mir_body(body_with_facts);
        let proof_asserts = find_proof_asserts_in_mir(tcx, mir_body, contract.local_def_id);

        for pa in &proof_asserts {
            let (leading_assumptions, trusted_assumption, warnings) =
                collect_trusted_proof_assert_assumptions_for_assert(
                    tcx,
                    pa,
                    user_specs,
                    logic_fn_defs,
                );
            warning_count += warnings;
            if !leading_assumptions.is_empty() {
                assumptions_by_fn
                    .entry(pa.containing_fn)
                    .or_default()
                    .extend(leading_assumptions);
            }
            if let Some(assumption) = trusted_assumption {
                assumptions_by_fn
                    .entry(pa.containing_fn)
                    .or_default()
                    .push(assumption);
            }
        }
    }

    (assumptions_by_fn, warning_count)
}

pub(in crate::callbacks) fn collect_trusted_proof_assert_assumptions_for_assert(
    tcx: TyCtxt<'_>,
    proof_assert: &crate::proof_assert::ProofAssert,
    user_specs: &HashMap<DefId, StdSpec>,
    logic_fn_defs: &[LogicFnDef],
) -> (Vec<PureExpr>, Option<PureExpr>, usize) {
    let logic_method_names: HashSet<String> = logic_fn_defs
        .iter()
        .filter(|logic_fn| {
            logic_fn
                .params()
                .first()
                .is_some_and(|param| param == "self")
        })
        .map(|logic_fn| logic_fn.name().to_string())
        .collect();
    let (leading_assumptions, _) = collect_leading_proof_assert_assumptions(
        tcx,
        proof_assert,
        logic_fn_defs,
        user_specs,
        &logic_method_names,
    );

    if !proof_assert.trusted {
        return (leading_assumptions, None, 0);
    }

    let Some(expr_text) = proof_assert.expr_text.as_ref() else {
        let fn_path = tcx.def_path_str(proof_assert.containing_fn);
        warn!("trusted proof_assert in {fn_path} has no expression");
        return (leading_assumptions, None, 0);
    };

    let logic_fn_path_map = build_logic_fn_path_map(logic_fn_defs);
    match parse_contract_body(expr_text) {
        Ok(expr) => {
            let expr =
                super::super::logic_fn_scope::normalize_logic_fn_names(expr, &logic_fn_path_map);
            (leading_assumptions, Some(expr), 0)
        }
        Err(e) => {
            let fn_path = tcx.def_path_str(proof_assert.containing_fn);
            debug!(
                "trust-wp: warning: dropped trusted proof_assert in {fn_path}: '{expr_text}': {e}"
            );
            (leading_assumptions, None, 1)
        }
    }
}
