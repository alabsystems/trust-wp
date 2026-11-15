// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared closure receiver identity helpers.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{Body, Local, Rvalue, StatementKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_logic_fn_arity, tuple_logic_fn_name},
    PureExpr,
};

use super::super::try_get_body_with_context;
use crate::mir_analysis::get_mir_body;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::callbacks) struct ClosureReceiverBinding {
    pub(in crate::callbacks) def_id: DefId,
    pub(in crate::callbacks) receiver_name: String,
}

fn source_name_for_local(body: &Body<'_>, local: Local) -> Option<String> {
    for info in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &info.value {
            if place.local == local && place.projection.is_empty() {
                return Some(info.name.to_string());
            }
        }
    }
    None
}

pub(in crate::callbacks) fn collect_closure_receiver_bindings(
    tcx: TyCtxt<'_>,
    parent_local_def_id: LocalDefId,
) -> Vec<ClosureReceiverBinding> {
    let Some(body_with_facts) = try_get_body_with_context(tcx, parent_local_def_id) else {
        return Vec::new();
    };
    let mir_body: &Body<'_> = get_mir_body(&body_with_facts);

    let mut bindings = Vec::new();
    let mut seen_pairs = HashSet::new();
    let mut receiver_names = HashMap::<String, HashSet<DefId>>::new();

    for bb_data in mir_body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            let StatementKind::Assign((
                place,
                Rvalue::Aggregate(rustc_middle::mir::AggregateKind::Closure(def_id, _), _),
            )) = &stmt.kind
            else {
                continue;
            };

            let Some(receiver_name) = source_name_for_local(mir_body, place.local) else {
                continue;
            };

            if !seen_pairs.insert((*def_id, receiver_name.clone())) {
                continue;
            }

            receiver_names
                .entry(receiver_name.clone())
                .or_default()
                .insert(*def_id);
            bindings.push(ClosureReceiverBinding {
                def_id: *def_id,
                receiver_name,
            });
        }
    }

    bindings
        .into_iter()
        .filter(|binding| {
            receiver_names
                .get(&binding.receiver_name)
                .is_some_and(|def_ids| def_ids.len() == 1)
        })
        .collect()
}

/// Doc markers of the closures trust-wp's macros emit as CARRIERS only: the
/// `proof_assert!` / `__trust_wp_trusted_proof_assert!` / `proof_by!` lambda
/// (`let _ = #[doc = "trust-wp:proof_assert:.."] || -> bool { true };`) is
/// dropped where it is built and is never passed to anything, so it is never
/// the receiver of a `precondition` / `postcondition*` call.
const CARRIER_CLOSURE_MARKERS: &[&str] = &[
    "trust-wp:proof_assert:",
    "trust-wp:trusted_proof_assert:",
    "trust-wp:proof_by:",
];

fn is_carrier_closure(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.get_all_attrs(def_id).iter().any(|attr| {
        crate::attr_utils::doc_marker_str(attr).is_some_and(|value| {
            let value = value.as_str();
            CARRIER_CLOSURE_MARKERS
                .iter()
                .any(|marker| value.starts_with(marker))
        })
    })
}

/// The closures of `parent_local_def_id`'s body that OWN their lowered
/// environment shape: `def_id -> capture count` for every closure aggregate
/// in the MIR that is the ONLY non-carrier closure of that capture count.
///
/// A closure environment lowers to `__trust_wp_tuple<N>(captures..)`
/// (`translate/rvalue.rs`), a term made of the capture VALUES that carries no
/// closure identity — two capture-less closures both lower to
/// `__trust_wp_tuple0()`, and `|| x += 1` lowers to `__trust_wp_tuple1(0)`
/// when `x == 0`. Such a term in receiver position of a Fn-trait spec call
/// can only come from an aggregate of THIS body (a parameter, a call result
/// or a field is a variable or a projection, never a constructor), so it
/// denotes a closure of this body of that arity; when exactly one exists the
/// receiver IS that closure, when several do nothing tells them apart and no
/// environment term denotes any of them.
pub(in crate::callbacks) fn collect_sole_env_owners(
    tcx: TyCtxt<'_>,
    parent_local_def_id: LocalDefId,
) -> HashMap<DefId, usize> {
    let Some(body_with_facts) = try_get_body_with_context(tcx, parent_local_def_id) else {
        return HashMap::new();
    };
    let mir_body: &Body<'_> = get_mir_body(&body_with_facts);

    let mut arities: HashMap<DefId, usize> = HashMap::new();
    for bb_data in mir_body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            let StatementKind::Assign((
                _,
                Rvalue::Aggregate(rustc_middle::mir::AggregateKind::Closure(def_id, _), _),
            )) = &stmt.kind
            else {
                continue;
            };
            let Some(local_def_id) = def_id.as_local() else {
                continue;
            };
            let carrier = is_carrier_closure(tcx, *def_id);
            let arity = tcx.closure_captures(local_def_id).len();
            tracing::debug!(
                closure = %tcx.def_path_str(*def_id),
                arity,
                carrier,
                "closure aggregate in body (env owner census)"
            );
            if carrier {
                continue;
            }
            arities.insert(*def_id, arity);
        }
    }

    let mut per_arity: HashMap<usize, usize> = HashMap::new();
    for arity in arities.values() {
        *per_arity.entry(*arity).or_default() += 1;
    }
    arities
        .into_iter()
        .filter(|(_, arity)| per_arity.get(arity) == Some(&1))
        .collect()
}

/// The arity of a closure-environment constructor receiver
/// (`__trust_wp_tuple<N>(..)` under any `Deref` / `Final` / `Old` / `View`
/// wrappers), or `None` for any other receiver shape.
pub(in crate::callbacks) fn closure_env_ctor_arity(expr: &PureExpr) -> Option<usize> {
    match expr {
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => closure_env_ctor_arity(inner),
        // `tuple_logic_fn_arity` rejects arity 0 (the unit tuple has no fields
        // to project), but a capture-less closure's environment IS
        // `__trust_wp_tuple0()` (`translate/rvalue.rs`), so arity 0 is a
        // closure-environment arity here.
        PureExpr::LogicFnCall { name, args } if args.is_empty() => {
            (*name == tuple_logic_fn_name(0)).then_some(0)
        }
        PureExpr::LogicFnCall { name, args } => {
            tuple_logic_fn_arity(name).filter(|arity| *arity == args.len())
        }
        _ => None,
    }
}

pub(in crate::callbacks) fn closure_receiver_base_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => closure_receiver_base_name(inner),
        _ => None,
    }
}
