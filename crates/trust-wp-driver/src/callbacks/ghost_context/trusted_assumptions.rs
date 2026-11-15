// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trusted `proof_assert!` assumption collection.
//!
//! Iterates over contracts, detects proof_asserts via MIR, and collects
//! trusted trailing expressions and leading lemma-call postconditions.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{
        Body, Local, Location, StatementKind, TerminatorKind, VarDebugInfoContents, START_BLOCK,
    },
    ty::TyCtxt,
};
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
        let Some(body_with_facts) = try_get_body_with_context(tcx, contract.local_def_id) else {
            continue;
        };
        let mir_body = get_mir_body(&body_with_facts);
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
            let Some(assumption) = trusted_assumption else {
                continue;
            };
            let refusal = match pa.location {
                Some(location) => trusted_assertion_entry_refusal(mir_body, location, &assumption),
                None => Some("its program point is unknown".to_string()),
            };
            if let Some(why) = refusal {
                eprintln!(
                    "trust-wp: proof_assert in {}::{} trusted: not assumed ({why}); \
                     the function is proved without it",
                    tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE),
                    tcx.def_path_str(pa.containing_fn)
                );
                continue;
            }
            assumptions_by_fn
                .entry(pa.containing_fn)
                .or_default()
                .push(assumption);
        }
    }

    (assumptions_by_fn, warning_count)
}

/// Why a trusted `proof_assert!` may not be assumed at function ENTRY, or
/// `None` when it may.
///
/// The trusted expression joins the containing function's `effective_requires`
/// (`enrich_effective_clauses`), so it is assumed of the entry state, while
/// Creusot assumes it where it is written (`-{e}-`). The two readings agree only
/// when every execution reaches the assertion before anything that owes a proof,
/// holding the entry value of every name the expression reads: the MIR from the
/// start block to the assertion is one straight line (no branch, call, assertion,
/// drop or loop), nothing on it writes an argument or through a reference, and
/// each name read is exactly one argument local. Anywhere else a fact true where
/// it stands proves a false postcondition (trusted_pa_later_write,
/// trusted_pa_shadowed), lends one branch's premise to another
/// (trusted_pa_branch), or discharges an earlier obligation
/// (trusted_pa_after_obligation).
pub(in crate::callbacks) fn trusted_assertion_entry_refusal(
    body: &Body<'_>,
    location: Location,
    expr: &PureExpr,
) -> Option<String> {
    let is_arg = |local: Local| (1..=body.arg_count).contains(&local.as_usize());
    let mut block = START_BLOCK;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(block) {
            return Some("a loop precedes it".to_string());
        }
        let data = &body.basic_blocks[block];
        let end = if block == location.block {
            location.statement_index.min(data.statements.len())
        } else {
            data.statements.len()
        };
        for statement in &data.statements[..end] {
            match &statement.kind {
                StatementKind::Assign((place, _)) => {
                    if place.is_indirect() {
                        return Some("a write through a reference precedes it".to_string());
                    }
                    if is_arg(place.local) {
                        return Some("a write to an argument precedes it".to_string());
                    }
                }
                StatementKind::StorageLive(..)
                | StatementKind::StorageDead(..)
                | StatementKind::FakeRead(..)
                | StatementKind::PlaceMention(..)
                | StatementKind::AscribeUserType(..)
                | StatementKind::Coverage(..)
                | StatementKind::ConstEvalCounter
                | StatementKind::Nop => {}
                _ => {
                    return Some(
                        "a statement the entry check does not model precedes it".to_string(),
                    )
                }
            }
        }
        if block == location.block {
            break;
        }
        block = match &data.terminator().kind {
            TerminatorKind::Goto { target, .. } => *target,
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => *real_target,
            _ => return Some("a branch, call, assertion or drop precedes it".to_string()),
        };
    }

    // A name bound more than once (a shadowing `let`), through a projection
    // (a destructured argument, a closure capture) or to a constant is not
    // read as the argument at entry.
    let mut bindings: HashMap<String, Vec<Option<Local>>> = HashMap::new();
    for info in &body.var_debug_info {
        let local = match &info.value {
            VarDebugInfoContents::Place(place) if place.projection.is_empty() => Some(place.local),
            _ => None,
        };
        bindings
            .entry(info.name.to_string())
            .or_default()
            .push(local);
    }
    let mut names: Vec<String> = expr.free_vars().into_iter().collect();
    names.sort();
    for name in names {
        match bindings.get(&name).map(Vec::as_slice) {
            Some([Some(local)]) if is_arg(*local) => {}
            _ => return Some(format!("`{name}` does not name exactly one argument")),
        }
    }
    None
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
        .map(|logic_fn| logic_fn.short_name().to_string())
        .collect();
    let (leading_assumptions, _) = collect_leading_proof_assert_assumptions(
        tcx,
        proof_assert,
        logic_fn_defs,
        user_specs,
        &logic_method_names,
    );

    // The lemma calls and the trusted expression are written beside the
    // assertion and name its bindings; one whose binding cannot be told is
    // no fact (D-237).
    let leading_assumptions: Vec<PureExpr> = leading_assumptions
        .into_iter()
        .filter_map(|fact| {
            crate::mir_analysis::binding_identity::resolve_proof_assert_bindings(
                tcx,
                proof_assert,
                &fact,
            )
            .ok()
        })
        .collect();
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
            match crate::mir_analysis::binding_identity::resolve_proof_assert_bindings(
                tcx,
                proof_assert,
                &expr,
            ) {
                Ok(expr) => (leading_assumptions, Some(expr), 0),
                Err(name) => {
                    let fn_path = tcx.def_path_str(proof_assert.containing_fn);
                    debug!(
                        "trust-wp: warning: dropped trusted proof_assert in {fn_path}: \
                         `{name}` names no one binding there (D-237)"
                    );
                    (leading_assumptions, None, 1)
                }
            }
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
