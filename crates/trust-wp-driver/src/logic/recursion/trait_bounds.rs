// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive-trait-bound validation for logic trait methods.
//!
//! Faithful port of Creusot's "Illegal recursive trait" check
//! (`reference/creusot/creusot/src/validate/recursive_types.rs`, `add_trait`
//! + `check_recursion`) scoped to the logic-function lane.
//!
//! A trait is *recursive through its bounds* when the trait-bound graph —
//! supertrait edges plus every trait bound appearing on one of the trait's own
//! associated items (method where-clauses, `impl Trait` argument bounds,
//! associated-type bounds) — contains a cycle through the trait. A logic
//! method of such a trait is an inconsistency vector: its contract is admitted
//! for callers while its definition can dispatch back into itself through the
//! bound (`x.f(x)` on `x: impl Q` inside `Q::f`, `self.f(self)` under
//! `where Self: Tr<Self>`, or through a supertrait `P: Q` bound), so the
//! "definition" never terminates and `#[ensures(false)]` becomes provable.
//! Creusot rejects the trait declaration outright
//! (tests/should_fail/recursive_types/impl_arg.rs,
//! terminates/trait_where.rs, terminates/trait_where_supertrait.rs); trust-wp
//! must too — the termination callgraph cannot see these edges because they
//! exist in the *typing context*, not in any body.
//!
//! ## Soundness (PARAMOUNT)
//! The check is a definition-level reject: no body analysis, no attempt to
//! prove the dispatch harmless. Any cycle in the bound graph that reaches a
//! trait with local logic methods fails those methods' obligations. A
//! `#[variant(...)]` cannot discharge it — the recursion is admitted by the
//! typing context before any variant is compared — matching Creusot, which
//! offers no escape hatch for an illegal recursive trait.

use std::collections::{HashMap, HashSet};

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{self, TyCtxt};

use super::{super::discovery::has_logic_marker, LogicRecursionError};

/// Collect errors for every local logic method (trait declaration or trait
/// impl) whose trait is recursive through its bounds.
pub(super) fn collect_recursive_trait_bound_errors(tcx: TyCtxt<'_>) -> Vec<LogicRecursionError> {
    let graph = build_trait_bound_graph(tcx);
    if graph.edges.is_empty() {
        return Vec::new();
    }

    let recursive_traits: HashSet<DefId> = graph
        .edges
        .keys()
        .copied()
        .filter(|&trait_def_id| bound_graph_reaches(&graph.edges, trait_def_id, trait_def_id))
        .collect();
    if recursive_traits.is_empty() {
        return Vec::new();
    }

    let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
    let mut errors = Vec::new();
    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::AssocFn) {
            continue;
        }
        if !has_logic_marker(tcx.get_all_attrs(def_id)) {
            continue;
        }
        let Some(trait_def_id) = container_trait_of_assoc_fn(tcx, def_id) else {
            continue;
        };
        if !recursive_traits.contains(&trait_def_id) {
            continue;
        }
        let witness = graph
            .cycle_witness(trait_def_id)
            .map_or_else(String::new, |witness| format!(" ({witness})"));
        errors.push(LogicRecursionError {
            full_path: format!("{crate_name}::{}", tcx.def_path_str(def_id)),
            message: format!(
                "illegal recursive trait: `{}` is recursive through its bounds{witness}; \
                 the typing context lets this logic definition dispatch back into itself, \
                 so termination cannot be verified",
                tcx.def_path_str(trait_def_id)
            ),
        });
    }
    errors
}

/// The local trait-bound graph plus a human-readable description per edge.
struct TraitBoundGraph {
    /// `trait -> traits reachable in one bound step` (supertraits, method
    /// bounds, associated-type bounds). Only local traits have entries;
    /// foreign bound traits appear as edge targets without outgoing edges,
    /// mirroring Creusot's local-only `add_trait` iteration.
    edges: HashMap<DefId, HashSet<DefId>>,
    /// First recorded bound description per `(trait, bound-trait)` edge,
    /// used for diagnostics.
    edge_descriptions: HashMap<(DefId, DefId), String>,
}

impl TraitBoundGraph {
    /// Describe the first outgoing edge of `trait_def_id` that lies on a cycle
    /// back to it (skipping non-cycle bounds such as `Self: Sized`).
    fn cycle_witness(&self, trait_def_id: DefId) -> Option<&str> {
        let successors = self.edges.get(&trait_def_id)?;
        let mut on_cycle: Vec<DefId> = successors
            .iter()
            .copied()
            .filter(|&successor| {
                successor == trait_def_id
                    || bound_graph_reaches(&self.edges, successor, trait_def_id)
            })
            .collect();
        on_cycle.sort_by_key(|def_id| (def_id.krate.as_u32(), def_id.index.as_u32()));
        on_cycle.into_iter().find_map(|successor| {
            self.edge_descriptions
                .get(&(trait_def_id, successor))
                .map(String::as_str)
        })
    }
}

fn build_trait_bound_graph(tcx: TyCtxt<'_>) -> TraitBoundGraph {
    let mut graph = TraitBoundGraph {
        edges: HashMap::new(),
        edge_descriptions: HashMap::new(),
    };

    for local_def_id in tcx.iter_local_def_id() {
        let trait_def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(trait_def_id), DefKind::Trait) {
            continue;
        }
        let mut successors = HashSet::new();

        // Supertrait edges. `trait_explicit_clauses_and_bounds` carries the
        // user-written trait predicates WITHOUT the implicit identity
        // `Self: Trait` that plain `clauses_of` appends for traits — the
        // identity predicate would fabricate a self-loop on every trait.
        for (clause, _span) in tcx.trait_explicit_clauses_and_bounds(local_def_id).clauses {
            if let ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() {
                let target = predicate.trait_ref.def_id;
                successors.insert(target);
                graph
                    .edge_descriptions
                    .entry((trait_def_id, target))
                    .or_insert_with(|| {
                        format!(
                            "`{}` is a supertrait bound of the trait",
                            tcx.def_path_str(target)
                        )
                    });
            }
        }

        // Associated-item bound edges: method where-clauses and `impl Trait`
        // argument bounds (own predicates of the method — the parent trait's
        // predicates are NOT included, so no identity self-loop), plus
        // associated-type bounds.
        for item in tcx.associated_items(trait_def_id).in_definition_order() {
            match item.kind {
                ty::AssocKind::Fn { .. } => {
                    for (clause, _span) in tcx.clauses_of(item.def_id).clauses {
                        if let ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() {
                            let target = predicate.trait_ref.def_id;
                            successors.insert(target);
                            graph
                                .edge_descriptions
                                .entry((trait_def_id, target))
                                .or_insert_with(|| {
                                    format!(
                                        "`{}` is a bound of `{}`",
                                        tcx.def_path_str(target),
                                        tcx.def_path_str(item.def_id)
                                    )
                                });
                        }
                    }
                }
                ty::AssocKind::Type { .. } => {
                    for (clause, _span) in tcx.explicit_item_bounds(item.def_id).skip_binder() {
                        if let ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() {
                            let target = predicate.trait_ref.def_id;
                            successors.insert(target);
                            graph
                                .edge_descriptions
                                .entry((trait_def_id, target))
                                .or_insert_with(|| {
                                    format!(
                                        "`{}` is a bound of `{}`",
                                        tcx.def_path_str(target),
                                        tcx.def_path_str(item.def_id)
                                    )
                                });
                        }
                    }
                }
                ty::AssocKind::Const { .. } => {}
            }
        }

        graph.edges.insert(trait_def_id, successors);
    }

    graph
}

/// Is `target` reachable from `start` through at least one bound edge?
/// (`start == target` detects a cycle through the trait itself.)
fn bound_graph_reaches(
    edges: &HashMap<DefId, HashSet<DefId>>,
    start: DefId,
    target: DefId,
) -> bool {
    let mut visited = HashSet::new();
    let mut stack: Vec<DefId> = edges
        .get(&start)
        .map(|successors| successors.iter().copied().collect())
        .unwrap_or_default();
    while let Some(node) = stack.pop() {
        if node == target {
            return true;
        }
        if !visited.insert(node) {
            continue;
        }
        if let Some(successors) = edges.get(&node) {
            stack.extend(successors.iter().copied());
        }
    }
    false
}

/// The trait a logic `AssocFn` belongs to: the parent for a trait-declaration
/// method, or the implemented trait method's parent for a trait-impl method.
/// Inherent-impl methods have no trait and are exempt.
fn container_trait_of_assoc_fn(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    let assoc = tcx.opt_associated_item(def_id)?;
    match assoc.container {
        ty::AssocContainer::Trait => Some(tcx.parent(def_id)),
        ty::AssocContainer::TraitImpl(trait_item) => {
            trait_item.ok().map(|trait_method| tcx.parent(trait_method))
        }
        ty::AssocContainer::InherentImpl => None,
    }
}
