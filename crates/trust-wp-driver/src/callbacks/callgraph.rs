// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call graph utilities for recursion-aware termination checks.
//!
//! Phase 2 termination work uses MIR call edges to detect recursion and enforce
//! that `#[check(terminates)]` recursive functions provide a variant.
//!
//! Mutual recursion is detected via SCC analysis so it cannot silently bypass
//! termination checks. A mutual-recursive `#[check(terminates)]` SCC is accepted
//! structurally when every member declares a `#[variant(...)]`. Proving that the
//! variant tuples decrease lexicographically at every call site is deferred —
//! trust-wp currently accepts the structural shape and emits a TODO trace per SCC.

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use rustc_hir::{def_id::DefId, Node, TraitFn, TraitItemKind};
use rustc_middle::{
    mir::{Operand, TerminatorKind},
    ty::{GenericArgKind, GenericArgs, GenericArgsRef, TyCtxt},
};

use super::{
    super::{attr_utils::has_check_mode, contracts::FunctionContract, mir_analysis::get_mir_body},
    try_get_body_with_context,
};

/// Direct-call graph: caller -> direct callees.
pub(super) type CallGraph = HashMap<DefId, HashSet<DefId>>;

/// Per-function termination validation errors.
pub(super) type TerminationErrors = HashMap<DefId, Vec<String>>;

/// Build a direct call graph from MIR bodies reachable from discovered contracts.
///
/// This walks through local helper callees even if they have no contracts, so
/// recursion through unannotated intermediates still participates in SCC
/// detection and termination structural checks.
pub(super) fn build_call_graph(tcx: TyCtxt<'_>, contracts: &[FunctionContract]) -> CallGraph {
    let roots = contracts.iter().map(|contract| contract.def_id);
    build_reachable_call_graph(roots, |def_id| collect_direct_local_callees(tcx, def_id))
}

fn collect_direct_local_callees(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<DefId> {
    // Skip extern/non-local items: MIR is unavailable from this crate callback.
    let Some(local_def_id) = def_id.as_local() else {
        return HashSet::new();
    };

    // Skip declarations without MIR bodies (e.g., trait method signatures).
    if !tcx.is_mir_available(def_id) {
        return HashSet::new();
    }

    // Skip bodyless trait method declarations. `is_mir_available` returns true
    // for these (rustc generates an unreachable shim), but `mir_borrowck` panics
    // in `body_owned_by` because no HIR body exists. This guard matches the
    // pattern in parsing.rs:464 (#972) and prevents ICEs on trait-heavy crates.
    if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
        if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
            return HashSet::new();
        }
    }

    // Ensure borrowck MIR is available in the callback cache.
    let root = tcx
        .typeck_root_def_id(local_def_id.to_def_id())
        .expect_local();
    let _ = tcx.mir_borrowck(root);

    let mut callees = HashSet::new();
    if let Some(body_with_facts) = try_get_body_with_context(local_def_id) {
        let body = get_mir_body(body_with_facts);
        for bb_data in body.basic_blocks.iter() {
            if let TerminatorKind::Call { func, .. } = &bb_data.terminator().kind {
                if let Operand::Constant(box constant) = func {
                    if let rustc_middle::ty::TyKind::FnDef(callee, substs) =
                        constant.const_.ty().kind()
                    {
                        // Try to resolve trait method calls to their concrete impl.
                        // MIR encodes `obj.method()` as FnDef(TraitMethod, [ConcreteType]),
                        // so without resolution, recursion through trait dispatch is invisible.
                        let resolved =
                            try_resolve_trait_impl(tcx, *callee, substs).unwrap_or(*callee);
                        if resolved.as_local().is_some() {
                            callees.insert(resolved);
                        }
                        // Keep the original trait method DefId ONLY when resolution
                        // failed (resolved == *callee), so trait-default self-recursion
                        // is still detected. When resolution succeeds, the resolved impl
                        // DefId is sufficient — keeping the original trait method DefId
                        // causes false termination errors when the trait method lacks
                        // #[check(terminates)] but the concrete impl has it (#2701).
                        if resolved == *callee && callee.as_local().is_some() {
                            callees.insert(*callee);
                        }

                        // Conservative edge addition for unresolved generic trait
                        // calls (#2665). When a call targets a trait method with
                        // unresolved type parameters, the concrete callee is
                        // unknown at analysis time. Conservatively add edges to
                        // ALL local impl methods of that trait method so SCC
                        // detection can find cycles through generic dispatch
                        // (e.g., `bar<I>` calling `I::Item::foo()` where the
                        // impl of `foo` calls `bar`).
                        let has_unresolved = substs.iter().any(|arg| {
                            arg.as_type().is_some_and(|ty| {
                                matches!(
                                    ty.kind(),
                                    rustc_middle::ty::TyKind::Param(..)
                                        | rustc_middle::ty::TyKind::Alias(..)
                                )
                            })
                        });
                        if has_unresolved {
                            callees.extend(find_all_local_impl_methods(tcx, *callee));
                        }
                    }
                }
            }
        }
    }

    callees
}

fn build_reachable_call_graph<T, I, F>(roots: I, mut direct_callees: F) -> HashMap<T, HashSet<T>>
where
    T: Eq + Hash + Copy,
    I: IntoIterator<Item = T>,
    F: FnMut(T) -> HashSet<T>,
{
    let roots: Vec<T> = roots.into_iter().collect();
    let mut visited = HashSet::new();
    let mut graph = HashMap::new();
    let mut worklist = roots.clone();

    while let Some(node) = worklist.pop() {
        if !visited.insert(node) {
            continue;
        }

        let callees = direct_callees(node);
        for callee in &callees {
            if !visited.contains(callee) {
                worklist.push(*callee);
            }
        }
        graph.insert(node, callees);
    }

    for root in roots {
        graph.entry(root).or_default();
    }

    graph
}

/// Detect all recursive functions: direct self-edges and mutual-recursion cycles.
pub(super) fn detect_recursive_nodes(graph: &CallGraph) -> HashSet<DefId> {
    detect_recursive_nodes_in_cycles(graph)
}

/// Detect functions that participate in mutual-recursion cycles only.
pub(super) fn detect_mutual_recursion(graph: &CallGraph) -> HashSet<DefId> {
    detect_mutual_recursive_nodes(graph)
}

/// Detect mutual-recursion SCCs restricted to `#[check(terminates)]` functions.
///
/// Returns the strongly connected components (size > 1) of the subgraph induced
/// by `terminates_set`. Each returned `HashSet<DefId>` is one mutual-recursion
/// group whose termination must be proved as a whole.
///
/// Self-recursive singletons are excluded — those are already covered by the
/// general recursive-needs-variant check. Edges that leave the terminates set
/// are dropped, so a terminates function calling a non-terminates helper that
/// happens to participate in an unrelated cycle does not contaminate the
/// terminates SCC analysis.
///
/// TODO: lex-tuple decrease at every call site within an SCC is not yet
/// enforced — `validate_recursive_termination_nodes` accepts an SCC as soon as
/// every member declares a `#[variant(...)]`. Solving variant values per call
/// site is multi-day work tracked separately.
///
/// Currently exercised only by unit tests; wired into the structural validator
/// once the lex-tuple decrease proof is implemented (trust-wp#7).
#[allow(dead_code)]
pub(super) fn detect_scc_for_mutual_terminates(
    call_graph: &CallGraph,
    terminates_set: &HashSet<DefId>,
) -> Vec<HashSet<DefId>> {
    // Project the call graph onto the terminates subset so cross-edges to
    // non-terminating helpers do not influence SCC membership.
    let restricted: HashMap<DefId, HashSet<DefId>> = terminates_set
        .iter()
        .map(|node| {
            let callees = call_graph
                .get(node)
                .map(|set| set.intersection(terminates_set).copied().collect())
                .unwrap_or_default();
            (*node, callees)
        })
        .collect();

    strongly_connected_components(&restricted)
        .into_iter()
        .filter(|component| component.len() > 1)
        .map(|component| component.into_iter().collect())
        .collect()
}

/// Validate phase-2 recursion requirements.
///
/// Current rule:
/// - A function marked `#[check(terminates)]` that is recursive must
///   provide at least one `#[variant(...)]` clause.
/// - A function marked `#[check(terminates)]` that is mutually recursive is
///   rejected (mutual-recursive variant ordering is not implemented yet).
pub(super) fn validate_recursive_termination_requirements(
    contracts: &[FunctionContract],
    recursive_functions: &HashSet<DefId>,
    mutual_recursive_functions: &HashSet<DefId>,
) -> TerminationErrors {
    let nodes: Vec<TerminationNode<DefId>> = contracts
        .iter()
        .map(|contract| TerminationNode {
            id: contract.def_id,
            terminates: contract.terminates,
            has_variant: !contract.variants.is_empty(),
            is_mutual_recursive: mutual_recursive_functions.contains(&contract.def_id),
            trusted: contract.trusted,
        })
        .collect();

    validate_recursive_termination_nodes(&nodes, recursive_functions)
}

/// Reject `#[check(terminates)]` functions that participate in a mutual-recursion
/// cycle (SCC of size > 1), including cycles closed via unannotated helpers.
///
/// Lex-tuple decrease across mutual-recursive SCCs is not yet implemented
/// (trust-wp#7). Rather than silently passing through to variant decrease
/// verification — where the per-function MIR walk finds no self-call sites
/// and emits a confusing "detected as recursive but no call sites found in MIR"
/// diagnostic — we flag the cycle here and short-circuit further termination
/// validation for those functions.
///
/// The cycle includes both `#[check(terminates)]` peers (e.g.
/// `mutual_non_decreasing_a` ↔ `mutual_non_decreasing_b`) and indirect cycles
/// through unannotated helpers (e.g. `terminates_fn` → `helper_no_marker` →
/// `terminates_fn`). The latter pattern would otherwise surface as a
/// "callee not marked #[check(terminates)]" error, which describes a symptom
/// rather than the root cause.
///
/// Returns the per-function diagnostic map AND the set of terminates DefIds
/// flagged so callers can suppress duplicate diagnostics from the callee/
/// recursive-variant validators.
pub(super) fn validate_terminates_mutual_recursion_unsupported(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    call_graph: &CallGraph,
) -> (TerminationErrors, HashSet<DefId>) {
    let terminates_set: HashSet<DefId> = contracts
        .iter()
        .filter(|c| c.terminates && !c.trusted)
        .map(|c| c.def_id)
        .collect();

    let mut errors: TerminationErrors = HashMap::new();
    let mut flagged: HashSet<DefId> = HashSet::new();

    if terminates_set.is_empty() {
        return (errors, flagged);
    }

    // SCCs over the full reachable call graph — so cycles closed through
    // unannotated helpers are still detected.
    for component in strongly_connected_components(call_graph) {
        if component.len() < 2 {
            continue;
        }
        let scc: HashSet<DefId> = component.iter().copied().collect();
        let terminates_members: Vec<DefId> = component
            .iter()
            .copied()
            .filter(|id| terminates_set.contains(id))
            .collect();
        if terminates_members.is_empty() {
            continue;
        }

        for member in &terminates_members {
            // Build a stable list of the other cycle members for the
            // diagnostic. Prefer terminates peers when both kinds exist;
            // otherwise list unannotated helpers as the via-path.
            let mut peers: Vec<String> = scc
                .iter()
                .filter(|id| *id != member)
                .map(|id| tcx.def_path_str(*id))
                .collect();
            peers.sort();
            let peers_joined = peers.join(", ");
            let member_name = tcx.def_path_str(*member);
            errors.entry(*member).or_default().push(format!(
                "mutual recursion in #[check(terminates)] is not yet supported: \
                     `{member_name}` participates in a cycle with {peers_joined}"
            ));
            flagged.insert(*member);
        }
    }

    (errors, flagged)
}

/// Validate that `#[check(terminates)]` functions only call other
/// `#[check(terminates)]` or logic functions.
///
/// In Creusot, a function marked `#[check(terminates)]` must not call
/// any local function that is not also marked `#[check(terminates)]` or
/// `#[logic]`. Calling a non-terminating function from a terminating one
/// invalidates the termination guarantee.
pub(super) fn validate_terminates_callee_requirements(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    call_graph: &CallGraph,
) -> TerminationErrors {
    let terminates_set: HashSet<DefId> = contracts
        .iter()
        .filter(|c| c.terminates)
        .map(|c| c.def_id)
        .collect();

    // Build a ghost function set from contracts (ghost functions are implicitly terminating).
    let ghost_set: HashSet<DefId> = contracts
        .iter()
        .filter(|c| c.ghost)
        .map(|c| c.def_id)
        .collect();

    // Trusted functions are axiomatic — including their termination behavior.
    // A `#[check(terminates)]` caller may call a `#[trusted]` callee even
    // when the trusted callee lacks an explicit terminates marker (e.g.
    // Creusot's `#[trusted(terminates)]` is the canonical pattern, but the
    // marker arg is currently a hint trust-wp accepts but does not consume).
    let trusted_set: HashSet<DefId> = contracts
        .iter()
        .filter(|c| c.trusted)
        .map(|c| c.def_id)
        .collect();

    let mut errors = HashMap::new();

    for contract in contracts {
        if !contract.terminates {
            continue;
        }

        if let Some(callees) = call_graph.get(&contract.def_id) {
            for callee in callees {
                // Skip external/non-local callees (we assume stdlib terminates)
                if callee.as_local().is_none() {
                    continue;
                }

                // Logic functions are implicitly terminating — check directly
                // on the callee's attributes (logic functions may not be in
                // the contracts list).
                let callee_attrs = tcx.get_all_attrs(*callee);
                if super::super::logic::has_logic_marker(callee_attrs) {
                    continue;
                }

                // Ghost functions are implicitly terminating
                if ghost_set.contains(callee) {
                    continue;
                }

                // Trusted callees are axiomatic — termination is assumed.
                if trusted_set.contains(callee) {
                    continue;
                }
                // Trusted ancestry: a callee inside a `#[trusted] mod` or
                // a callee that's directly `#[trusted]` but missing from
                // the contracts list is also assumed terminating.
                if super::discovery::trusted::has_trusted_marker(tcx, *callee, callee_attrs) {
                    continue;
                }

                // #[check(terminates)] callees are fine
                if terminates_set.contains(callee) {
                    continue;
                }

                // Also check if the callee itself has a terminates marker
                // (it might not be in our contracts list but still annotated)
                if super::super::attr_utils::has_check_mode(callee_attrs, "terminates") {
                    continue;
                }

                // Trait method specialization fallback (#2671): the call graph
                // resolution may keep the original trait method DefId when
                // `Instance::try_resolve` fails in the callback context. Before
                // emitting an error, check if any local concrete impl of this
                // trait method has `#[check(terminates)]`. This handles the
                // Creusot pattern where the trait declaration omits terminates
                // but the concrete impl provides it (e.g., `purity.rs`).
                if let Some(assoc) = tcx.opt_associated_item(*callee) {
                    if matches!(assoc.container, rustc_middle::ty::AssocContainer::Trait) {
                        let trait_def_id = tcx.parent(*callee);
                        let method_name = tcx.item_name(*callee);
                        let impl_has_terminates = tcx.iter_local_def_id().any(|local| {
                            let impl_def_id = local.to_def_id();
                            if !matches!(
                                tcx.def_kind(impl_def_id),
                                rustc_hir::def::DefKind::Impl { of_trait: true }
                            ) {
                                return false;
                            }
                            let iref = tcx.impl_trait_ref(impl_def_id).skip_binder();
                            if iref.def_id != trait_def_id {
                                return false;
                            }
                            tcx.associated_items(impl_def_id)
                                .in_definition_order()
                                .any(|item| {
                                    item.name() == method_name
                                        && has_check_mode(
                                            tcx.get_all_attrs(item.def_id),
                                            "terminates",
                                        )
                                })
                        });
                        if impl_has_terminates {
                            continue;
                        }
                    }
                }

                let callee_name = tcx.def_path_str(*callee);
                errors
                    .entry(contract.def_id)
                    .or_insert_with(Vec::new)
                    .push(format!(
                        "#[check(terminates)] function calls `{callee_name}` \
                         which is not marked #[check(terminates)]"
                    ));
            }
        }
    }

    errors
}

/// Reject direct polymorphic self-recursion.
///
/// A recursive call to the same `DefId` with different type/const arguments is
/// not the same termination problem as ordinary structural recursion. Creusot
/// rejects it before attempting variant decrease, because `foo::<T>` calling
/// `foo::<u32>` does not decrease the original well-founded argument.
pub(super) fn validate_polymorphic_recursive_calls(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
) -> TerminationErrors {
    let mut errors = HashMap::new();

    for contract in contracts {
        if !contract.terminates {
            continue;
        }
        if polymorphic_self_call_changes_args(tcx, contract.def_id) {
            errors.entry(contract.def_id).or_insert_with(Vec::new).push(
                "polymorphic recursion in #[check(terminates)] is not supported: \
                     recursive call changes generic arguments"
                    .to_string(),
            );
        }
    }

    errors
}

fn polymorphic_self_call_changes_args(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(local_def_id) = def_id.as_local() else {
        return false;
    };
    if !tcx.is_mir_available(def_id) {
        return false;
    }

    let root = tcx
        .typeck_root_def_id(local_def_id.to_def_id())
        .expect_local();
    let _ = tcx.mir_borrowck(root);

    let Some(body_with_facts) = try_get_body_with_context(local_def_id) else {
        return false;
    };
    let body = get_mir_body(body_with_facts);
    let identity_args = GenericArgs::identity_for_item(tcx, def_id);

    body.basic_blocks.iter().any(|bb_data| {
        let TerminatorKind::Call { func, .. } = &bb_data.terminator().kind else {
            return false;
        };
        let Operand::Constant(box constant) = func else {
            return false;
        };
        let rustc_middle::ty::TyKind::FnDef(callee, args) = constant.const_.ty().kind() else {
            return false;
        };
        *callee == def_id && non_region_generic_args_differ(args, identity_args)
    })
}

fn non_region_generic_args_differ<'tcx>(
    actual: GenericArgsRef<'tcx>,
    expected: GenericArgsRef<'tcx>,
) -> bool {
    let mut actual_non_region = actual
        .iter()
        .filter(|arg| !matches!(arg.kind(), GenericArgKind::Lifetime(_)));
    let mut expected_non_region = expected
        .iter()
        .filter(|arg| !matches!(arg.kind(), GenericArgKind::Lifetime(_)));

    loop {
        match (actual_non_region.next(), expected_non_region.next()) {
            (None, None) => return false,
            (Some(_), None) | (None, Some(_)) => return true,
            (Some(actual_arg), Some(expected_arg)) => {
                if actual_arg.kind() != expected_arg.kind() {
                    return true;
                }
            }
        }
    }
}

/// Validate that `#[check(terminates)]` functions with loops provide
/// loop variants.
///
/// In Creusot, loops in a `#[check(terminates)]` function must have a
/// `#[variant]` clause to prove termination. A loop without a variant
/// in a terminating function is a structural error.
pub(super) fn validate_terminates_loop_variant_requirements(
    contracts: &[FunctionContract],
) -> TerminationErrors {
    let mut errors = HashMap::new();

    for contract in contracts {
        if !contract.terminates {
            continue;
        }

        // Check if the function has loops but no loop variants.
        // `all_loop_spans` tracks ALL loops in the function body (from HIR),
        // including those without any contract annotations.
        if contract.all_loop_spans.is_empty() {
            continue;
        }

        // Count loops that have variants (from per_loop_variants).
        let loops_with_variants: HashSet<(u32, u32)> = contract
            .per_loop_variants
            .iter()
            .map(|(start, end, _)| (*start, *end))
            .collect();

        for (start, end) in &contract.all_loop_spans {
            if !loops_with_variants.contains(&(*start, *end)) {
                // Also check function-level variants as fallback — a single
                // `#[variant(x)]` on the function covers all its loops.
                if contract.variants.is_empty() {
                    errors.entry(contract.def_id).or_insert_with(Vec::new).push(
                        "loop in #[check(terminates)] function requires \
                             #[variant(...)] for termination proof"
                            .to_string(),
                    );
                    // Only report once per function (not per loop)
                    break;
                }
            }
        }
    }

    errors
}

/// Validate that trait-impl check modes agree.
///
/// When a trait method declares `#[check(terminates)]` or `#[check(ghost)]`,
/// the impl method MUST also declare the same check mode. Conversely, an impl
/// must not add a check mode that differs from the trait's declared mode.
///
/// In Creusot, this produces errors like:
/// "Expected `f` to be `#[check(terminates)]` as specified by the trait declaration"
pub(super) fn validate_trait_impl_check_mode_agreement(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
) -> TerminationErrors {
    let mut errors = HashMap::new();

    for contract in contracts {
        let Some(ref origin) = contract.trait_origin else {
            continue;
        };

        // Look up the trait method's DefId from the trait's associated items.
        let trait_method_def_id = tcx
            .associated_items(origin.trait_def_id)
            .in_definition_order()
            .find(|item| item.name().as_str() == origin.trait_method_name)
            .map(|item| item.def_id);

        let Some(trait_method_def_id) = trait_method_def_id else {
            continue;
        };

        // Get the trait method's attributes to check its declared check modes.
        let trait_method_attrs = tcx.get_all_attrs(trait_method_def_id);
        let trait_terminates = has_check_mode(trait_method_attrs, "terminates");
        let trait_ghost = has_check_mode(trait_method_attrs, "ghost");

        // If the trait method has no check modes, nothing to validate.
        if !trait_terminates && !trait_ghost {
            continue;
        }

        let method_name = &origin.trait_method_name;

        // Check each declared mode.
        if trait_terminates && !contract.terminates {
            errors
                .entry(contract.def_id)
                .or_insert_with(Vec::new)
                .push(format!(
                    "Expected `{method_name}` to be `#[check(terminates)]` \
                     as specified by the trait declaration"
                ));
        }

        if trait_ghost && !contract.ghost {
            errors
                .entry(contract.def_id)
                .or_insert_with(Vec::new)
                .push(format!(
                    "Expected `{method_name}` to be `#[check(ghost)]` \
                     as specified by the trait declaration"
                ));
        }
    }

    errors
}

/// Validate that `#[check(terminates)]` impl methods do not call default
/// trait methods from the same trait that are not `#[logic]` functions.
///
/// In Creusot, calling a non-logic default trait method from an impl method
/// on the same trait is treated as potential mutual recursion because:
/// - The default method could be overridden in another impl
/// - That override could call back into the current method
/// - So `impl_g -> default_f -> (potential override) -> impl_g` is a cycle
///
/// This is a conservative check that matches Creusot's behavior (#2665).
pub(super) fn validate_default_trait_method_mutual_recursion(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    call_graph: &CallGraph,
) -> TerminationErrors {
    let mut errors = HashMap::new();

    for contract in contracts {
        if !contract.terminates {
            continue;
        }

        // Only check impl methods (methods that implement a trait).
        let Some(ref origin) = contract.trait_origin else {
            continue;
        };

        let Some(callees) = call_graph.get(&contract.def_id) else {
            continue;
        };

        let impl_trait_def_id = origin.trait_def_id;

        for callee in callees {
            // Check if the callee is a trait item (default method) on the same trait.
            let Some(assoc_item) = tcx.opt_associated_item(*callee) else {
                continue;
            };
            if !matches!(
                assoc_item.container,
                rustc_middle::ty::AssocContainer::Trait
            ) {
                continue;
            }

            // Is it on the same trait as our impl?
            let callee_trait_def_id = tcx.parent(*callee);
            if callee_trait_def_id != impl_trait_def_id {
                continue;
            }

            // Check if the callee has a default body (i.e., it's a provided method).
            // Required methods (no body) are not the issue here.
            let callee_local = callee.as_local();
            let is_default_impl = callee_local.map_or(false, |local_id| {
                if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_id) {
                    matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Provided(_)))
                } else {
                    false
                }
            });

            if !is_default_impl {
                continue;
            }

            // Skip logic functions — they are axiomatic and don't participate
            // in runtime mutual recursion.
            let callee_attrs = tcx.get_all_attrs(*callee);
            if super::super::logic::has_logic_marker(callee_attrs) {
                continue;
            }

            let callee_name = tcx.def_path_str(*callee);
            let method_name = &origin.trait_method_name;
            errors
                .entry(contract.def_id)
                .or_insert_with(Vec::new)
                .push(format!(
                    "Mutually recursive functions: `{method_name}` calls default \
                     trait method `{callee_name}` which might call `{method_name}` \
                     via trait dispatch"
                ));
        }
    }

    errors
}

/// Try to resolve a trait method call to its concrete impl method.
///
/// MIR represents trait method calls as `FnDef(trait_method_def_id, [ConcreteType, ...])`.
/// Without resolution, the callgraph sees trait method DefIds instead of impl method DefIds,
/// making recursion through trait dispatch invisible to SCC detection.
///
/// Uses `Instance::try_resolve` for monomorphic calls, with a fallback that scans
/// local trait impls when the primary resolution fails (e.g., for non-codegen contexts).
fn try_resolve_trait_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
    substs: GenericArgsRef<'tcx>,
) -> Option<DefId> {
    // Only trait method calls need resolution.
    let assoc_item = tcx.opt_associated_item(callee_def_id)?;
    if !matches!(
        assoc_item.container,
        rustc_middle::ty::AssocContainer::Trait
    ) {
        return None;
    }

    // The trait DefId is the parent of the trait method DefId.
    let trait_def_id = tcx.parent(callee_def_id);

    // Primary path: Instance::try_resolve for fully monomorphic calls.
    // Guard: skip resolution when substs contain unresolved type parameters or
    // projection aliases — fully_monomorphized() + normalize_erasing_regions
    // ICEs on polymorphic types like `FnMut<(I::Item, Snapshot<Seq<I::Item>>)>`.
    use rustc_middle::ty::{Instance, TypingEnv};
    let has_unresolved_params = substs.iter().any(|arg| {
        arg.as_type().is_some_and(|ty| {
            matches!(
                ty.kind(),
                rustc_middle::ty::TyKind::Param(..) | rustc_middle::ty::TyKind::Alias(..)
            )
        })
    });
    if has_unresolved_params {
        return None;
    }
    let typing_env = TypingEnv::fully_monomorphized();
    if let Ok(Some(instance)) = Instance::try_resolve(tcx, typing_env, callee_def_id, substs) {
        let resolved_def_id = instance.def_id();
        if resolved_def_id.as_local().is_some() && resolved_def_id != callee_def_id {
            return Some(resolved_def_id);
        }
    }

    // Fallback: scan local trait impls for matching Self type and method name.
    // This catches cases where Instance::try_resolve fails (e.g., non-codegen context).
    let self_ty = substs.types().next()?;
    // Skip polymorphic Self types — we can only match concrete impls.
    if matches!(
        self_ty.kind(),
        rustc_middle::ty::TyKind::Param(..) | rustc_middle::ty::TyKind::Alias(..)
    ) {
        return None;
    }
    let method_name = tcx.item_name(callee_def_id);
    for scan_local in tcx.iter_local_def_id() {
        let impl_def_id = scan_local.to_def_id();
        if !matches!(
            tcx.def_kind(impl_def_id),
            rustc_hir::def::DefKind::Impl { of_trait: true }
        ) {
            continue;
        }
        let impl_trait_ref = tcx.impl_trait_ref(impl_def_id).skip_binder();
        if impl_trait_ref.def_id != trait_def_id {
            continue;
        }
        if impl_trait_ref.self_ty() != self_ty {
            continue;
        }
        for assoc in tcx.associated_items(impl_def_id).in_definition_order() {
            if assoc.name() == method_name
                && matches!(tcx.def_kind(assoc.def_id), rustc_hir::def::DefKind::AssocFn)
                && assoc.def_id.as_local().is_some()
            {
                return Some(assoc.def_id);
            }
        }
    }
    None
}

/// Find ALL local impl methods that implement a given trait method.
///
/// When a function calls a trait method with unresolved type parameters
/// (e.g., `I::Item::foo()` where `I` is generic), we cannot determine the
/// concrete callee. This function returns all local implementations of
/// that trait method so the callgraph conservatively includes edges to
/// every possible dispatch target. This enables SCC detection to find
/// cycles through generic trait dispatch (#2665).
fn find_all_local_impl_methods(tcx: TyCtxt<'_>, callee_def_id: DefId) -> Vec<DefId> {
    let mut results = Vec::new();

    // Only trait method calls need expansion.
    let Some(assoc_item) = tcx.opt_associated_item(callee_def_id) else {
        return results;
    };
    if !matches!(
        assoc_item.container,
        rustc_middle::ty::AssocContainer::Trait
    ) {
        return results;
    }

    let trait_def_id = tcx.parent(callee_def_id);
    let method_name = tcx.item_name(callee_def_id);

    // Scan all local impls of this trait for the target method.
    for scan_local in tcx.iter_local_def_id() {
        let impl_def_id = scan_local.to_def_id();
        if !matches!(
            tcx.def_kind(impl_def_id),
            rustc_hir::def::DefKind::Impl { of_trait: true }
        ) {
            continue;
        }
        let impl_trait_ref = tcx.impl_trait_ref(impl_def_id).skip_binder();
        if impl_trait_ref.def_id != trait_def_id {
            continue;
        }
        for assoc in tcx.associated_items(impl_def_id).in_definition_order() {
            if assoc.name() == method_name
                && matches!(tcx.def_kind(assoc.def_id), rustc_hir::def::DefKind::AssocFn)
                && assoc.def_id.as_local().is_some()
            {
                results.push(assoc.def_id);
            }
        }
    }

    results
}

#[derive(Clone, Copy)]
struct TerminationNode<T> {
    id: T,
    terminates: bool,
    has_variant: bool,
    /// Reserved for SCC-aware diagnostics and future lex-tuple decrease
    /// proof scheduling (trust-wp#7). Currently set by callers but not read
    /// by `validate_recursive_termination_nodes` — mutual-recursive nodes
    /// are already covered by the `recursive_nodes` check.
    #[allow(dead_code)]
    is_mutual_recursive: bool,
    /// Trusted functions are exempt from termination validation —
    /// their behavior (including termination) is taken as axiomatic
    /// by the verifier. Creusot's `#[trusted(terminates)]` pattern
    /// relies on this: the function carries a termination hint but
    /// the actual termination is not checked.
    trusted: bool,
}

fn detect_self_recursive_nodes<T>(graph: &HashMap<T, HashSet<T>>) -> HashSet<T>
where
    T: Eq + Hash + Copy,
{
    graph
        .iter()
        .filter_map(|(caller, callees)| callees.contains(caller).then_some(*caller))
        .collect()
}

fn detect_recursive_nodes_in_cycles<T>(graph: &HashMap<T, HashSet<T>>) -> HashSet<T>
where
    T: Eq + Hash + Copy,
{
    let self_recursive_nodes = detect_self_recursive_nodes(graph);
    let mut recursive_nodes = HashSet::new();

    for component in strongly_connected_components(graph) {
        if component.len() > 1 {
            recursive_nodes.extend(component);
            continue;
        }

        if let Some(node) = component.first().copied() {
            if self_recursive_nodes.contains(&node) {
                recursive_nodes.insert(node);
            }
        }
    }

    recursive_nodes
}

fn detect_mutual_recursive_nodes<T>(graph: &HashMap<T, HashSet<T>>) -> HashSet<T>
where
    T: Eq + Hash + Copy,
{
    strongly_connected_components(graph)
        .into_iter()
        .filter(|component| component.len() > 1)
        .flat_map(|component| component.into_iter())
        .collect()
}

fn strongly_connected_components<T>(graph: &HashMap<T, HashSet<T>>) -> Vec<Vec<T>>
where
    T: Eq + Hash + Copy,
{
    struct Tarjan<'a, T>
    where
        T: Eq + Hash + Copy,
    {
        graph: &'a HashMap<T, HashSet<T>>,
        index: usize,
        indices: HashMap<T, usize>,
        lowlink: HashMap<T, usize>,
        stack: Vec<T>,
        on_stack: HashSet<T>,
        components: Vec<Vec<T>>,
    }

    impl<'a, T> Tarjan<'a, T>
    where
        T: Eq + Hash + Copy,
    {
        fn new(graph: &'a HashMap<T, HashSet<T>>) -> Self {
            Self {
                graph,
                index: 0,
                indices: HashMap::new(),
                lowlink: HashMap::new(),
                stack: Vec::new(),
                on_stack: HashSet::new(),
                components: Vec::new(),
            }
        }

        fn run(mut self) -> Vec<Vec<T>> {
            for node in self.graph.keys().copied() {
                if !self.indices.contains_key(&node) {
                    self.strong_connect(node);
                }
            }
            self.components
        }

        fn strong_connect(&mut self, node: T) {
            let current_index = self.index;
            self.index += 1;
            self.indices.insert(node, current_index);
            self.lowlink.insert(node, current_index);
            self.stack.push(node);
            self.on_stack.insert(node);

            if let Some(callees) = self.graph.get(&node) {
                for callee in callees {
                    if !self.graph.contains_key(callee) {
                        continue;
                    }

                    if !self.indices.contains_key(callee) {
                        self.strong_connect(*callee);
                        let callee_lowlink = *self
                            .lowlink
                            .get(callee)
                            .expect("callee lowlink missing after DFS visit");
                        let node_lowlink = self
                            .lowlink
                            .get_mut(&node)
                            .expect("node lowlink missing during DFS backtrack");
                        *node_lowlink = (*node_lowlink).min(callee_lowlink);
                    } else if self.on_stack.contains(callee) {
                        let callee_index = *self
                            .indices
                            .get(callee)
                            .expect("callee index missing for in-stack node");
                        let node_lowlink = self
                            .lowlink
                            .get_mut(&node)
                            .expect("node lowlink missing during back-edge processing");
                        *node_lowlink = (*node_lowlink).min(callee_index);
                    }
                }
            }

            if self.lowlink.get(&node) == self.indices.get(&node) {
                let mut component = Vec::new();
                while let Some(stack_node) = self.stack.pop() {
                    self.on_stack.remove(&stack_node);
                    component.push(stack_node);
                    if stack_node == node {
                        break;
                    }
                }
                self.components.push(component);
            }
        }
    }

    Tarjan::new(graph).run()
}

fn validate_recursive_termination_nodes<T>(
    nodes: &[TerminationNode<T>],
    recursive_nodes: &HashSet<T>,
) -> HashMap<T, Vec<String>>
where
    T: Eq + Hash + Copy,
{
    // Mutual recursion handling (Phase 7, trust-wp#7):
    //
    // trust-wp previously rejected every `#[check(terminates)]` function that
    // participated in a mutual-recursion cycle. The Creusot approach is to
    // form the SCC of all `#[check(terminates)]` callees and require each
    // SCC member to declare a `#[variant(...)]`; the variant tuples must
    // then decrease lexicographically at every call site.
    //
    // The structural half (every SCC member declares a variant) is enforced
    // here through the same `recursive_function ... requires #[variant(...)]`
    // diagnostic used for direct self-recursion — nodes in a mutual cycle are
    // already members of `recursive_nodes`, so the single per-node variant
    // check applies uniformly to direct and mutual recursion.
    //
    // TODO(trust-wp#7): prove lex-tuple decrease per call site. Until then we
    // accept the structural shape and let the obligation generator emit the
    // per-call-site variant-decrease lemmas when it gains SCC awareness.
    let mut errors = HashMap::new();

    for node in nodes {
        // Trusted functions skip termination validation entirely — their
        // termination (and all other behavior) is taken as axiomatic.
        // Creusot's `#[trusted(terminates)]` pattern on recursive
        // functions relies on this (see specification/trusted.rs).
        if node.trusted {
            continue;
        }

        if node.terminates && recursive_nodes.contains(&node.id) && !node.has_variant {
            errors.entry(node.id).or_insert_with(Vec::new).push(
                "recursive function marked #[check(terminates)] requires #[variant(...)]"
                    .to_string(),
            );
        }
    }

    errors
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detect_self_recursion_finds_only_self_edges() {
        let mut graph: HashMap<u8, HashSet<u8>> = HashMap::new();
        graph.insert(1, HashSet::from([1, 2]));
        graph.insert(2, HashSet::from([3]));
        graph.insert(3, HashSet::from([3]));

        let recursive = detect_self_recursive_nodes(&graph);

        assert_eq!(recursive, HashSet::from([1, 3]));
    }

    #[test]
    fn detect_recursive_nodes_includes_mutual_cycles_and_self_edges() {
        let mut graph: HashMap<u8, HashSet<u8>> = HashMap::new();
        graph.insert(1, HashSet::from([2]));
        graph.insert(2, HashSet::from([1]));
        graph.insert(3, HashSet::from([3]));
        graph.insert(4, HashSet::from([5]));
        graph.insert(5, HashSet::new());

        let recursive = detect_recursive_nodes_in_cycles(&graph);

        assert_eq!(recursive, HashSet::from([1, 2, 3]));
    }

    #[test]
    fn detect_mutual_recursion_excludes_direct_self_edges() {
        let mut graph: HashMap<u8, HashSet<u8>> = HashMap::new();
        graph.insert(1, HashSet::from([2]));
        graph.insert(2, HashSet::from([1]));
        graph.insert(3, HashSet::from([3]));

        let mutual = detect_mutual_recursive_nodes(&graph);

        assert_eq!(mutual, HashSet::from([1, 2]));
    }

    #[test]
    fn build_reachable_call_graph_expands_through_non_root_helpers() {
        let adjacency: HashMap<u8, HashSet<u8>> = HashMap::from([
            // Root contract function.
            (1u8, HashSet::from([2u8])),
            // Helper function with no contract (non-root) that closes the cycle.
            (2u8, HashSet::from([1u8])),
        ]);

        let graph = build_reachable_call_graph([1u8], |node| {
            adjacency.get(&node).cloned().unwrap_or_default()
        });

        let expected_1 = HashSet::from([2u8]);
        let expected_2 = HashSet::from([1u8]);
        assert_eq!(graph.get(&1u8), Some(&expected_1));
        assert_eq!(graph.get(&2u8), Some(&expected_2));

        let recursive = detect_recursive_nodes_in_cycles(&graph);
        assert_eq!(recursive, HashSet::from([1u8, 2u8]));
    }

    #[test]
    fn build_reachable_call_graph_keeps_root_without_edges() {
        let graph = build_reachable_call_graph([9u8], |_| HashSet::new());
        let empty = HashSet::new();
        assert_eq!(graph.get(&9u8), Some(&empty));
    }

    #[test]
    fn validate_recursive_termination_requires_variant_for_recursive_terminates() {
        let nodes = vec![
            TerminationNode {
                id: 1u8,
                terminates: true,
                has_variant: false,
                is_mutual_recursive: false,
                trusted: false,
            },
            TerminationNode {
                id: 2u8,
                terminates: true,
                has_variant: true,
                is_mutual_recursive: false,
                trusted: false,
            },
            TerminationNode {
                id: 3u8,
                terminates: false,
                has_variant: false,
                is_mutual_recursive: false,
                trusted: false,
            },
        ];
        let recursive = HashSet::from([1u8, 2u8, 3u8]);

        let errors = validate_recursive_termination_nodes(&nodes, &recursive);

        assert_eq!(errors.len(), 1);
        assert!(errors.contains_key(&1u8));
    }

    #[test]
    fn validate_mutual_terminates_accepts_when_all_have_variants() {
        // Phase 7 (trust-wp#7): a mutual-recursion SCC where every member declares
        // a `#[variant(...)]` is accepted structurally. The per-call-site
        // lex-tuple decrease proof is deferred — see the TODO at
        // `validate_recursive_termination_nodes`.
        let nodes = vec![
            TerminationNode {
                id: 1u8,
                terminates: true,
                has_variant: true,
                is_mutual_recursive: true,
                trusted: false,
            },
            TerminationNode {
                id: 2u8,
                terminates: true,
                has_variant: true,
                is_mutual_recursive: true,
                trusted: false,
            },
        ];
        let recursive = HashSet::from([1u8, 2u8]);

        let errors = validate_recursive_termination_nodes(&nodes, &recursive);

        assert!(
            errors.is_empty(),
            "mutual-recursive SCC with variants on every member should be accepted, got {errors:?}"
        );
    }

    #[test]
    fn validate_mutual_terminates_rejects_when_any_member_lacks_variant() {
        // Phase 7 (trust-wp#7): when at least one SCC member is missing a
        // `#[variant(...)]`, the structural check fails with the existing
        // recursive-needs-variant diagnostic.
        let nodes = vec![
            TerminationNode {
                id: 1u8,
                terminates: true,
                has_variant: true,
                is_mutual_recursive: true,
                trusted: false,
            },
            TerminationNode {
                id: 2u8,
                terminates: true,
                has_variant: false, // missing
                is_mutual_recursive: true,
                trusted: false,
            },
        ];
        let recursive = HashSet::from([1u8, 2u8]);

        let errors = validate_recursive_termination_nodes(&nodes, &recursive);

        assert!(
            !errors.contains_key(&1u8),
            "node 1 has a variant and should be silent, got {errors:?}"
        );
        let node_2_errors = errors
            .get(&2u8)
            .expect("node 2 lacks a variant and should be rejected");
        assert!(
            node_2_errors
                .iter()
                .any(|msg| msg.contains("requires #[variant(...)]")),
            "expected variant-missing diagnostic for node 2, got {node_2_errors:?}"
        );
    }

    #[test]
    fn validate_terminates_loop_variant_reports_missing_loop_variant() {
        use rustc_hir::def_id::CRATE_DEF_ID;

        use crate::contracts::FunctionContract;

        // Create a synthetic DefId (crate 0, index 100).
        let def_id = DefId {
            krate: rustc_span::def_id::CrateNum::from_u32(0),
            index: rustc_hir::def_id::DefIndex::from_u32(100),
        };

        let contract = FunctionContract {
            local_def_id: CRATE_DEF_ID,
            def_id,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![],      // no loop variants
            all_loop_spans: vec![(10, 50)], // has a loop
            variants: vec![],               // no function-level variant
            terminates: true,
            ghost: false,
            trusted: false,
            trait_origin: None,
        };

        let errors = validate_terminates_loop_variant_requirements(&[contract]);

        assert_eq!(errors.len(), 1);
        assert!(
            errors
                .get(&def_id)
                .expect("missing loop-variant error")
                .iter()
                .any(|msg| msg.contains("loop") && msg.contains("variant")),
            "expected loop variant requirement diagnostic"
        );
    }

    #[test]
    fn validate_terminates_loop_variant_no_error_when_variant_present() {
        use rustc_hir::def_id::CRATE_DEF_ID;

        use crate::contracts::FunctionContract;

        let def_id = DefId {
            krate: rustc_span::def_id::CrateNum::from_u32(0),
            index: rustc_hir::def_id::DefIndex::from_u32(100),
        };

        let contract = FunctionContract {
            local_def_id: CRATE_DEF_ID,
            def_id,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![(10, 50, vec!["x".to_string()])], // loop has variant
            all_loop_spans: vec![(10, 50)],                           // has a loop
            variants: vec![],                                         // no function-level variant
            terminates: true,
            ghost: false,
            trusted: false,

            trait_origin: None,
        };

        let errors = validate_terminates_loop_variant_requirements(&[contract]);

        assert!(
            errors.is_empty(),
            "expected no errors when loop has variant"
        );
    }

    #[test]
    fn validate_terminates_loop_variant_no_error_with_function_level_variant() {
        use rustc_hir::def_id::CRATE_DEF_ID;

        use crate::contracts::FunctionContract;

        let def_id = DefId {
            krate: rustc_span::def_id::CrateNum::from_u32(0),
            index: rustc_hir::def_id::DefIndex::from_u32(100),
        };

        let contract = FunctionContract {
            local_def_id: CRATE_DEF_ID,
            def_id,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![],       // no per-loop variant
            all_loop_spans: vec![(10, 50)],  // has a loop
            variants: vec!["x".to_string()], // function-level variant covers it
            terminates: true,
            ghost: false,
            trusted: false,

            trait_origin: None,
        };

        let errors = validate_terminates_loop_variant_requirements(&[contract]);

        assert!(
            errors.is_empty(),
            "expected no errors when function has a variant clause"
        );
    }

    #[test]
    fn validate_terminates_loop_variant_no_error_for_non_terminates() {
        use rustc_hir::def_id::CRATE_DEF_ID;

        use crate::contracts::FunctionContract;

        let def_id = DefId {
            krate: rustc_span::def_id::CrateNum::from_u32(0),
            index: rustc_hir::def_id::DefIndex::from_u32(100),
        };

        let contract = FunctionContract {
            local_def_id: CRATE_DEF_ID,
            def_id,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![],
            all_loop_spans: vec![(10, 50)], // has a loop
            variants: vec![],
            terminates: false, // NOT a terminates function
            ghost: false,
            trusted: false,

            trait_origin: None,
        };

        let errors = validate_terminates_loop_variant_requirements(&[contract]);

        assert!(
            errors.is_empty(),
            "non-terminates function should not be checked for loop variants"
        );
    }

    #[test]
    fn detect_mutual_recursion_through_conservative_edges() {
        // Simulates the complicated_traits_recursion pattern:
        // Node 1 (i32::foo) -> Node 2 (bar)
        // Node 2 (bar) -> Node 3 (Foo::foo, trait default)
        // Without conservative edges, no cycle since Node 3 is a dead end.
        //
        // With conservative edges (bar has unresolved generic, so bar also
        // edges to Node 1), the cycle 1->2->1 is detected.
        let mut graph: HashMap<u8, HashSet<u8>> = HashMap::new();
        graph.insert(1, HashSet::from([2])); // i32::foo -> bar
        graph.insert(2, HashSet::from([1, 3])); // bar -> i32::foo (conservative), Foo::foo
        graph.insert(3, HashSet::new()); // Foo::foo (empty default)

        let mutual = detect_mutual_recursive_nodes(&graph);
        assert_eq!(
            mutual,
            HashSet::from([1, 2]),
            "should detect mutual recursion 1<->2 through conservative edges"
        );

        let recursive = detect_recursive_nodes_in_cycles(&graph);
        assert!(
            recursive.contains(&1) && recursive.contains(&2),
            "nodes 1 and 2 should be in a recursive cycle"
        );
    }

    #[test]
    fn validate_mutual_terminates_detected_through_conservative_edges() {
        // When conservative edges create a mutual recursion cycle,
        // validate_recursive_termination_nodes still reports the
        // structural variant-missing diagnostic on each SCC member that
        // lacks a `#[variant(...)]` clause. The member that declares a
        // variant is accepted (trust-wp#7, Phase 7).
        let nodes = vec![
            TerminationNode {
                id: 1u8,
                terminates: true,
                has_variant: true,
                is_mutual_recursive: true, // detected by SCC
                trusted: false,
            },
            TerminationNode {
                id: 2u8,
                terminates: true,
                has_variant: false,
                is_mutual_recursive: true, // detected by SCC
                trusted: false,
            },
        ];
        let recursive = HashSet::from([1u8, 2u8]);

        let errors = validate_recursive_termination_nodes(&nodes, &recursive);

        assert!(
            !errors.contains_key(&1u8),
            "node 1 has a variant and should be accepted, got {errors:?}"
        );
        let node_2_errors = errors
            .get(&2u8)
            .expect("node 2 lacks a variant and should be rejected");
        assert!(
            node_2_errors
                .iter()
                .any(|msg| msg.contains("requires #[variant(...)]")),
            "expected variant-missing diagnostic for node 2"
        );
    }

    #[test]
    fn detect_scc_for_mutual_terminates_finds_two_node_cycle() {
        use rustc_hir::def_id::DefIndex;
        use rustc_span::def_id::CrateNum;

        let a = DefId {
            krate: CrateNum::from_u32(0),
            index: DefIndex::from_u32(1),
        };
        let b = DefId {
            krate: CrateNum::from_u32(0),
            index: DefIndex::from_u32(2),
        };
        let helper = DefId {
            krate: CrateNum::from_u32(0),
            index: DefIndex::from_u32(3),
        };

        let mut call_graph: CallGraph = HashMap::new();
        call_graph.insert(a, HashSet::from([b, helper]));
        call_graph.insert(b, HashSet::from([a]));
        // `helper` is not in the terminates set; the SCC restricted to
        // terminates functions must skip it.
        call_graph.insert(helper, HashSet::from([a]));

        let terminates = HashSet::from([a, b]);
        let sccs = detect_scc_for_mutual_terminates(&call_graph, &terminates);

        assert_eq!(sccs.len(), 1, "expected one mutual-recursion SCC");
        let scc = &sccs[0];
        assert!(scc.contains(&a) && scc.contains(&b));
        assert!(!scc.contains(&helper));
    }

    #[test]
    fn detect_scc_for_mutual_terminates_excludes_self_recursive_singletons() {
        use rustc_hir::def_id::DefIndex;
        use rustc_span::def_id::CrateNum;

        let a = DefId {
            krate: CrateNum::from_u32(0),
            index: DefIndex::from_u32(1),
        };
        let mut call_graph: CallGraph = HashMap::new();
        call_graph.insert(a, HashSet::from([a])); // direct self recursion

        let terminates = HashSet::from([a]);
        let sccs = detect_scc_for_mutual_terminates(&call_graph, &terminates);

        assert!(
            sccs.is_empty(),
            "self-recursive singletons are not mutual-recursion SCCs"
        );
    }
}
