// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared closure receiver identity helpers.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir::{Body, Local, Rvalue, StatementKind};
use trust_wp_core::formula::PureExpr;

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
    parent_local_def_id: LocalDefId,
) -> Vec<ClosureReceiverBinding> {
    let Some(body_with_facts) = try_get_body_with_context(parent_local_def_id) else {
        return Vec::new();
    };
    let mir_body: &Body<'_> = get_mir_body(body_with_facts);

    let mut bindings = Vec::new();
    let mut seen_pairs = HashSet::new();
    let mut receiver_names = HashMap::<String, HashSet<DefId>>::new();

    for bb_data in mir_body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            let StatementKind::Assign(box (
                place,
                Rvalue::Aggregate(box rustc_middle::mir::AggregateKind::Closure(def_id, _), _),
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
