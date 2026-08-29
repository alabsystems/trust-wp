// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call graph construction and name lookup for logic-function recursion detection.
//!
//! Builds the logic-function call graph from parsed AST bodies and text scanning,
//! and provides name resolution for logic call targets.

use std::collections::{HashMap, HashSet};

use trust_wp_core::formula::{Pattern, PureExpr};

use super::{
    text_scan::{collect_logic_references_from_text, collect_non_self_method_call_names_from_text},
    LogicRecursionNode,
};

#[derive(Debug, Clone)]
pub(super) struct LogicNameLookup {
    pub(super) full_path_to_idx: HashMap<String, usize>,
    pub(super) name_to_indices: HashMap<String, Vec<usize>>,
}

pub(super) fn build_logic_name_lookup(nodes: &[LogicRecursionNode]) -> LogicNameLookup {
    let full_path_to_idx: HashMap<String, usize> = nodes
        .iter()
        .enumerate()
        .map(|(idx, node)| (node.full_path.clone(), idx))
        .collect();

    let mut name_to_indices: HashMap<String, Vec<usize>> = HashMap::new();
    for (idx, node) in nodes.iter().enumerate() {
        name_to_indices
            .entry(node.name.clone())
            .or_default()
            .push(idx);
    }

    LogicNameLookup {
        full_path_to_idx,
        name_to_indices,
    }
}

pub(super) fn build_logic_call_graph(
    nodes: &[LogicRecursionNode],
) -> HashMap<usize, HashSet<usize>> {
    let lookup = build_logic_name_lookup(nodes);
    let mut graph: HashMap<usize, HashSet<usize>> = HashMap::new();
    for idx in 0..nodes.len() {
        graph.entry(idx).or_default();
    }

    for (caller_idx, node) in nodes.iter().enumerate() {
        let mut referenced_names = HashSet::new();
        collect_logic_references(&node.body, &mut referenced_names);
        collect_logic_references_from_text(&node.body_text, &mut referenced_names);
        for req in &node.requires {
            collect_logic_references(req, &mut referenced_names);
        }
        for ens in &node.ensures {
            collect_logic_references(ens, &mut referenced_names);
        }

        for name in referenced_names {
            for callee_idx in
                resolve_logic_call_targets(&name, &lookup.full_path_to_idx, &lookup.name_to_indices)
            {
                graph.entry(caller_idx).or_default().insert(callee_idx);
                if is_self_dispatch_call(&name)
                    && nodes[callee_idx].is_trait_method
                    && matches!(
                        nodes[callee_idx].mode,
                        trust_wp_core::logic::LogicMode::OpenSelf
                    )
                {
                    // Conservative dispatch model: a trait default method called as
                    // `Self::method()` may call back into the current impl only
                    // under `open(self)` visibility.
                    graph.entry(caller_idx).or_default().insert(caller_idx);
                }
            }
        }
    }

    add_concrete_receiver_dispatch_edges(nodes, &lookup, &mut graph);
    add_self_named_method_dispatch_edges(nodes, &mut graph);

    graph
}

/// Add the self-edge for `self.m(...)` method calls inside the logic fn NAMED
/// `m` (the `terminates` trio class: trait_impl_where.rs). The receiver has
/// the enclosing impl's `Self` type, so the dispatch set provably contains the
/// caller itself — via the impl that defines the caller, a trait/supertrait
/// where-clause bound, or a trait default. Short-name resolution
/// (`resolve_logic_call_targets`) only accepts a UNIQUE name match, and the
/// trait declaration and its impls ALWAYS share the method name, so exactly
/// the recursive case was silently dropped from the walk. Wire the self-edge
/// directly so the self-edge machinery adjudicates the node (structural
/// decrease, variant proof, unconditional-recursion reject) instead of
/// skipping it. The compact-text fallback keeps PARSE-FAILED bodies
/// fail-closed (they then hit the unparseable-body reject); successfully
/// parsed bodies are adjudicated by the AST walk alone.
fn add_self_named_method_dispatch_edges(
    nodes: &[LogicRecursionNode],
    graph: &mut HashMap<usize, HashSet<usize>>,
) {
    for (idx, node) in nodes.iter().enumerate() {
        if node_has_self_named_self_dispatch(node) {
            graph.entry(idx).or_default().insert(idx);
        }
    }
}

fn node_has_self_named_self_dispatch(node: &LogicRecursionNode) -> bool {
    let mut found = false;
    node.body.for_each_recursive(|expr| {
        if let PureExpr::MethodCall {
            receiver, method, ..
        } = expr
        {
            if method == &node.name && receiver_is_self_dispatch(receiver) {
                found = true;
            }
        }
    });
    if found {
        return true;
    }
    // Compact-text fallback ONLY for parse-failed bodies: on a successfully
    // parsed body the AST walk above is authoritative, and raw source text
    // still contains comments/string literals — `// self.f(...)` in a doc
    // note must not fabricate a self-edge (and with it a spurious
    // termination reject) for a non-recursive logic fn.
    node.body_parse_failed
        && super::compact_text_has_self_named_dispatch(&node.body_text, &node.name)
}

/// Add conservative call-graph edges for method calls with non-self receivers
/// (e.g., `1i32.f()`, `a.deep_model()`) where text scanning cannot determine
/// the concrete impl. For each such method name, edge to every known logic
/// function whose `name` matches AND whose path indicates a trait impl
/// (`<...as ...>::` or `<impl ... for ...>::`). Cross-function only — self
/// edges from this source are intentionally omitted so the legacy heuristic
/// at `body_text_has_deep_model_dispatch` and field-method invariants
/// (e.g. `self.vec.view()` field collisions) remain unaffected.
fn add_concrete_receiver_dispatch_edges(
    nodes: &[LogicRecursionNode],
    lookup: &LogicNameLookup,
    graph: &mut HashMap<usize, HashSet<usize>>,
) {
    for (caller_idx, node) in nodes.iter().enumerate() {
        let mut method_names = HashSet::new();
        collect_non_self_method_call_names_from_text(&node.body_text, &mut method_names);
        for method_name in &method_names {
            let Some(candidate_indices) = lookup.name_to_indices.get(method_name) else {
                continue;
            };
            for &callee_idx in candidate_indices {
                if callee_idx == caller_idx {
                    continue;
                }
                // Only count trait-impl-style logic functions (paths like
                // `<T as Trait>::method` or `<impl Trait for T>::method`).
                // Non-impl bare functions sharing a name with a method call
                // are usually unrelated false positives.
                if !path_indicates_trait_impl(&nodes[callee_idx].full_path) {
                    continue;
                }
                // SOUND typed gate for `deep_model` dispatch (the spurious-SCC
                // bug): text scanning cannot tell whether `field.deep_model()`
                // recurses into a sibling concrete type or just a
                // primitive/generic, so the blanket rule above wired an edge to
                // EVERY in-crate `deep_model` impl — fabricating a
                // fully-connected SCC for non-recursive `#[derive(DeepModel)]`
                // impls (e.g. syntax/derive_macros/deep_model.rs). When the
                // caller carries typed dispatch targets resolved from the
                // implementing ADT's field types, only add the edge if the
                // callee is one of those targets. `None` (resolution did not
                // apply) DEFAULT-REJECTs by keeping the conservative blanket
                // edge. This keeps bug/459 (Box-mediated self-recursion; the
                // field `Box<A>` resolves back to `A`'s in-crate impl) and
                // bug/1565 (the `i32` receiver resolves to the in-crate
                // `<i32 as Tr>::f` — but that path is the `f` method, not
                // `deep_model`, so it is governed by `None`/blanket and stays).
                if method_name == "deep_model" {
                    if let Some(targets) = &node.deep_model_dispatch_targets {
                        if !targets.contains(&nodes[callee_idx].full_path) {
                            continue;
                        }
                    }
                }
                graph.entry(caller_idx).or_default().insert(callee_idx);
            }
        }
    }
}

fn path_indicates_trait_impl(full_path: &str) -> bool {
    (full_path.contains(" as ") && full_path.contains('<') && full_path.contains(">::"))
        || full_path.contains("<impl ")
}

pub(super) fn collect_logic_references(expr: &PureExpr, names: &mut HashSet<String>) {
    expr.for_each_recursive(|node| match node {
        PureExpr::MethodCall {
            receiver, method, ..
        } => {
            if receiver_is_self_dispatch(receiver) {
                names.insert(method.clone());
            }
        }
        PureExpr::Match { arms, .. } => {
            for arm in arms {
                collect_logic_references_in_pattern(&arm.pattern, names);
            }
        }
        PureExpr::LogicFnCall { name, .. } => {
            names.insert(name.clone());
        }
        _ => {}
    });
}

fn collect_logic_references_in_pattern(pattern: &Pattern, names: &mut HashSet<String>) {
    match pattern {
        Pattern::Wildcard | Pattern::Binding(_) => {}
        Pattern::Literal(expr) => collect_logic_references(expr, names),
        Pattern::Constructor {
            inner: Some(inner), ..
        } => {
            collect_logic_references_in_pattern(inner, names);
        }
        Pattern::Constructor { inner: None, .. } => {}
        Pattern::Tuple(elements) => {
            for element in elements {
                collect_logic_references_in_pattern(element, names);
            }
        }
        #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
        _ => {}
    }
}

pub(super) fn resolve_logic_call_targets(
    call_name: &str,
    full_path_to_idx: &HashMap<String, usize>,
    name_to_indices: &HashMap<String, Vec<usize>>,
) -> Vec<usize> {
    let mut targets = Vec::new();

    if let Some(&idx) = full_path_to_idx.get(call_name) {
        targets.push(idx);
    }

    if is_qualified_call_name(call_name) {
        let segment_suffix = format!("::{call_name}");
        for (path, &idx) in full_path_to_idx {
            // Require match at a `::` segment boundary to prevent "a::f" matching "ba::f".
            if path.ends_with(&segment_suffix) || path == call_name {
                targets.push(idx);
            }
        }
    }

    if let Some(indices) = name_to_indices.get(call_name) {
        if indices.len() == 1 {
            targets.push(indices[0]);
        }
    }

    if let Some(short_name) = call_name.rsplit("::").next() {
        if short_name != call_name {
            if let Some(indices) = name_to_indices.get(short_name) {
                if indices.len() == 1 {
                    targets.push(indices[0]);
                }
            }
        }
    }

    targets.sort_unstable();
    targets.dedup();
    targets
}

pub(super) fn is_self_dispatch_call(call_name: &str) -> bool {
    call_name.starts_with("Self::") || call_name.starts_with("self::")
}

pub(super) fn receiver_is_self_dispatch(receiver: &PureExpr) -> bool {
    match receiver {
        PureExpr::Var(name, _) => name == "self",
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => receiver_is_self_dispatch(inner),
        _ => false,
    }
}

fn is_qualified_call_name(call_name: &str) -> bool {
    call_name.contains("::") || call_name.starts_with('<')
}

#[allow(clippy::similar_names)] // caller_idx / callee_idx are domain-distinct
pub(super) fn edge_name(
    nodes: &[LogicRecursionNode],
    caller_idx: usize,
    callee_idx: usize,
) -> String {
    format!(
        "{} -> {}",
        nodes[caller_idx].full_path, nodes[callee_idx].full_path
    )
}

pub(super) fn self_edge_name(nodes: &[LogicRecursionNode], idx: usize) -> String {
    edge_name(nodes, idx, idx)
}
