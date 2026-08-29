// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logic function filtering for verification goals.
//!
//! This module computes which logic function definitions are needed
//! for a specific verification goal.
//!
//! # Key Functions
//!
//! - [`filter_logic_fns_for_goal`]: Computes transitive closure of needed logic functions
//!
//! # Algorithm
//!
//! Given logic function names directly referenced in a verification goal,
//! computes the full set of needed functions by expanding through:
//! - Function bodies (expressions using other logic functions)
//! - Requires clauses (preconditions may reference other functions)
//!
//! Uses fixed-point iteration until no new functions are discovered.
//!
//! # See Also
//!
//! - [`crate::verify`]: Uses filtered logic functions during verification
//! - [`crate::expr::collect_logic_fn_names`]: Extracts function names from expressions

use std::collections::HashSet;

use trust_wp_core::logic::LogicFnDef;

use crate::expr::collect_logic_fn_names;

fn retain_closure_postcondition_mut_companions(
    logic_fns: &[LogicFnDef],
    needed_names: &mut HashSet<String>,
) {
    let companion_names: Vec<String> = logic_fns
        .iter()
        .filter_map(|logic_fn| {
            if !needed_names.contains(logic_fn.name())
                && !needed_names.contains(logic_fn.full_path())
            {
                return None;
            }

            let candidate_names = [
                logic_fn.name().to_string(),
                logic_fn.full_path().to_string(),
            ];
            let mut_names: Vec<String> = candidate_names
                .into_iter()
                .filter_map(|name| {
                    if let Some(suffix) = name.strip_prefix("closure_postcondition_") {
                        if suffix.starts_with("once_") || suffix.starts_with("mut_") {
                            return None;
                        }
                        let (arity_raw, sort_sig) = suffix.split_once('_')?;
                        let post_arity = arity_raw.parse::<usize>().ok()?;
                        let sort_tags: Vec<&str> = sort_sig.split('_').collect();
                        if sort_tags.len() != post_arity || sort_tags.is_empty() {
                            return None;
                        }

                        let mut mut_tags = sort_tags
                            .iter()
                            .map(|tag| (*tag).to_string())
                            .collect::<Vec<_>>();
                        let insert_pos = mut_tags.len() - 1;
                        mut_tags.insert(insert_pos, sort_tags[0].to_string());
                        return Some(format!(
                            "closure_postcondition_mut_{}_{}",
                            post_arity + 1,
                            mut_tags.join("_")
                        ));
                    }

                    if name == "postcondition" {
                        return Some("postcondition_mut".to_string());
                    }

                    if name.ends_with("::postcondition") || name.ends_with(".postcondition") {
                        return Some(name.replacen("postcondition", "postcondition_mut", 1));
                    }

                    None
                })
                .collect();

            mut_names.into_iter().find(|mut_name| {
                logic_fns
                    .iter()
                    .any(|logic_fn| logic_fn.name() == mut_name || logic_fn.full_path() == mut_name)
            })
        })
        .collect();

    needed_names.extend(companion_names);
}

/// Filters logic function definitions to only those needed for a verification goal.
///
/// Given a set of logic function names directly referenced in a goal (precondition,
/// postcondition, or invariant), computes the transitive closure of all logic
/// functions needed. This includes functions called by other logic functions'
/// requires clauses and bodies.
///
/// # Algorithm
///
/// Uses fixed-point iteration: starting from `initial_names`, repeatedly expands
/// the set by examining each referenced logic function's requires clauses and body
/// until no new names are added.
///
/// # Complexity
///
/// The outer `while changed` loop iterates at most F times (where F = `logic_fns.len()`),
/// since each iteration must expand at least one new function or terminate. Each
/// iteration scans all F functions and their expression trees (total expression nodes E).
/// Worst case: O(F² × E). In practice F is small (single digits for typical trust-wp
/// programs), so this is not a bottleneck. If F grows large (>50 logic functions),
/// consider switching to a dependency-graph-based topological approach (#506 F5).
///
/// # Arguments
///
/// * `logic_fns` - All available logic function definitions
/// * `initial_names` - Logic function names directly referenced in the goal
#[cfg(test)]
#[cfg_attr(not(ay_performance_proofs), allow(dead_code))]
pub(crate) fn filter_logic_fns_for_goal(
    logic_fns: &[LogicFnDef],
    initial_names: &HashSet<String>,
) -> Vec<LogicFnDef> {
    let mut needed_names = initial_names.clone();
    // Resolve Self-parametric trait method references (see filter_logic_fn_indices_for_goal).
    let self_resolved: Vec<String> = needed_names
        .iter()
        .filter_map(|n| n.strip_prefix("Self::").map(str::to_owned))
        .collect();
    needed_names.extend(self_resolved);
    retain_closure_postcondition_mut_companions(logic_fns, &mut needed_names);

    let mut expanded = HashSet::new();
    let mut changed = true;

    while changed {
        changed = false;
        for logic_fn in logic_fns {
            if expanded.contains(logic_fn.full_path()) {
                continue;
            }
            if !needed_names.contains(logic_fn.name())
                && !needed_names.contains(logic_fn.full_path())
            {
                continue;
            }

            expanded.insert(logic_fn.full_path().to_owned());
            let before = needed_names.len();

            for req in logic_fn.requires() {
                collect_logic_fn_names(req, &mut needed_names);
            }
            collect_logic_fn_names(logic_fn.body(), &mut needed_names);

            if needed_names.len() != before {
                changed = true;
            }
        }
    }

    logic_fns
        .iter()
        .filter(|logic_fn| {
            needed_names.contains(logic_fn.name()) || needed_names.contains(logic_fn.full_path())
        })
        .cloned()
        .collect()
}

/// Like [`filter_logic_fns_for_goal`], but returns indices into the original
/// slice instead of cloned definitions. This avoids deep-cloning `LogicFnDef`
/// structs (including recursive `PureExpr` AST trees) when mode overrides are
/// used for module-level scoping. (#564)
pub(crate) fn filter_logic_fn_indices_for_goal(
    logic_fns: &[LogicFnDef],
    initial_names: &HashSet<String>,
) -> Vec<usize> {
    let mut needed_names = initial_names.clone();
    // Resolve Self-parametric trait method references: when the goal contains
    // `Self::method()`, add the bare `method` name so that logic functions
    // registered under their short name are included. Without this, the filter
    // misses trait methods referenced via `Self::` and the encoder creates
    // disconnected placeholder UFs instead of using the registered axiom.
    let self_resolved: Vec<String> = needed_names
        .iter()
        .filter_map(|n| n.strip_prefix("Self::").map(str::to_owned))
        .collect();
    needed_names.extend(self_resolved);
    retain_closure_postcondition_mut_companions(logic_fns, &mut needed_names);

    let mut expanded = HashSet::new();
    let mut changed = true;

    while changed {
        changed = false;
        for logic_fn in logic_fns {
            if expanded.contains(logic_fn.full_path()) {
                continue;
            }
            if !needed_names.contains(logic_fn.name())
                && !needed_names.contains(logic_fn.full_path())
            {
                continue;
            }

            expanded.insert(logic_fn.full_path().to_owned());
            let before = needed_names.len();

            for req in logic_fn.requires() {
                collect_logic_fn_names(req, &mut needed_names);
            }
            collect_logic_fn_names(logic_fn.body(), &mut needed_names);

            if needed_names.len() != before {
                changed = true;
            }
        }
    }

    // Reverse inclusion for spec axioms (#1296): include logic functions whose
    // `ensures` clauses reference functions already in `needed_names`. These
    // are lemmas (e.g., `id_mono`) whose spec axioms provide useful quantified
    // facts about functions the goal cares about (e.g., `id`).
    //
    // This matches Creusot's behavior where `spec_axioms` from logic functions
    // are emitted as module-level axioms visible to all proofs in scope.
    let mut spec_relevant: HashSet<String> = HashSet::new();
    let declared_logic_names: HashSet<&str> = logic_fns
        .iter()
        .flat_map(|logic_fn| [logic_fn.name(), logic_fn.full_path()])
        .collect();
    for logic_fn in logic_fns {
        if logic_fn.ensures().is_empty() {
            continue;
        }
        // Already included by forward closure
        if needed_names.contains(logic_fn.name()) || needed_names.contains(logic_fn.full_path()) {
            continue;
        }
        // Check if this logic function's ensures mentions any needed function
        let mut ensures_names = HashSet::new();
        for ens in logic_fn.ensures() {
            collect_logic_fn_names(ens, &mut ensures_names);
        }
        if ensures_names
            .iter()
            .any(|n| declared_logic_names.contains(n.as_str()) && needed_names.contains(n))
        {
            spec_relevant.insert(logic_fn.name().to_owned());
            spec_relevant.insert(logic_fn.full_path().to_owned());
        }
    }
    needed_names.extend(spec_relevant);

    logic_fns
        .iter()
        .enumerate()
        .filter(|(_, logic_fn)| {
            needed_names.contains(logic_fn.name()) || needed_names.contains(logic_fn.full_path())
        })
        .map(|(i, _)| i)
        .collect()
}
