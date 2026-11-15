// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
use tracing::debug;
use trust_wp_core::{contract_parser::parse_contract, formula::PureExpr, logic::LogicFnDef};
use trust_wp_driver::StdSpec;

use super::ProofAssertSetup;
use crate::{callbacks::logic_fn_scope::build_logic_fn_path_map, contracts::FunctionContract};

/// Build shared setup maps for proof assertion verification.
///
/// Returns the setup and the number of dropped requires clauses (warnings).
pub(in crate::callbacks) fn build_proof_assert_setup<'a>(
    tcx: TyCtxt<'_>,
    contracts: &'a [FunctionContract],
    logic_fn_defs: &[LogicFnDef],
    downstream_user_specs: &HashMap<DefId, StdSpec>,
) -> (ProofAssertSetup<'a>, usize) {
    // Use the downgraded user_specs where unverified logic function postconditions
    // have been cleared (#1878). This prevents proof_assert leading-call assumption
    // injection from materializing unproven postconditions.
    let user_specs = downstream_user_specs.clone();

    // Build a map from LocalDefId to function preconditions.
    let mut precondition_parse_errors = 0usize;
    let fn_preconditions: HashMap<LocalDefId, Vec<PureExpr>> = contracts
        .iter()
        .filter_map(|c| {
            let requires: Vec<PureExpr> = c
                .requires
                .iter()
                .filter_map(|s| match parse_contract(s) {
                    Ok(expr) => Some(expr),
                    Err(e) => {
                        let fn_path = tcx.def_path_str(c.def_id);
                        debug!(
                            "trust-wp: warning: dropped unparseable requires clause in {fn_path}: '{s}': {e}"
                        );
                        precondition_parse_errors += 1;
                        None
                    }
                })
                .collect();
            if requires.is_empty() {
                None
            } else {
                Some((c.local_def_id, requires))
            }
        })
        .collect();
    if precondition_parse_errors > 0 {
        debug!(
            "trust-wp: warning: {precondition_parse_errors} requires clause(s) dropped due to parse errors \u{2014} callers will not be checked against these preconditions"
        );
    }
    let contract_by_local: HashMap<LocalDefId, &FunctionContract> =
        contracts.iter().map(|c| (c.local_def_id, c)).collect();

    // Build a mapping from module-qualified logic function paths to their
    // registered short names. This fixes the name mismatch when proof_assert
    // expressions use qualified paths like `x::transparent()` but logic
    // functions are registered as `transparent` in SMT. (#746)
    let logic_fn_path_map = build_logic_fn_path_map(logic_fn_defs);
    let logic_method_names: HashSet<String> = logic_fn_defs
        .iter()
        .filter(|logic_fn| {
            logic_fn
                .params()
                .first()
                .is_some_and(|param| param == "self")
        })
        .map(|logic_fn| logic_fn.short_name().to_string())
        .collect();

    // Resolve crate-level const items for substitution into proof_assert
    // expressions, matching the const resolution in verify_contracts(). (#1588)
    let const_item_substitutions = crate::callbacks::const_items::const_item_substitutions(tcx);

    (
        ProofAssertSetup {
            fn_preconditions,
            const_item_substitutions,
            contract_by_local,
            logic_fn_path_map,
            logic_method_names,
            user_specs,
        },
        precondition_parse_errors,
    )
}
