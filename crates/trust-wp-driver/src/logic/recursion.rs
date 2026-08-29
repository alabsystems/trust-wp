// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function recursion validation.
//!
//! Detects mutual recursion among `#[logic]`/`#[predicate]` functions.
//! Direct recursion without `#[variant]` is allowed (Creusot-compatible).
//! Variant-annotated mutual recursion is accepted only for a narrow first slice:
//! parsed call sites, integer variants, and proven per-edge decrease.

mod call_edges;
mod graph;
mod scc;
mod structural;
mod text_scan;
mod trait_bounds;
mod variant;

use std::collections::HashSet;

use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    contract_parser::parse_contract,
    formula::{ExprSort, PureExpr},
    logic::LogicMode,
};

// Re-export for test access via `use super::*`.
use self::text_scan::collect_logic_references_from_text;
use self::{
    call_edges::collect_parsed_logic_call_edges,
    graph::{
        build_logic_call_graph, build_logic_name_lookup, collect_logic_references,
        resolve_logic_call_targets, LogicNameLookup,
    },
    scc::{has_self_edge, strongly_connected_components},
    variant::{
        try_prove_self_variant_decrease, validate_supported_mutual_recursion_scc,
        SelfVariantDecrease,
    },
};
use super::discovery::{find_logic_functions, to_logic_fn_def, LogicFunction};

/// Logic recursion validation error for a specific function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LogicRecursionError {
    /// Fully-qualified function path.
    pub(crate) full_path: String,
    /// Human-readable diagnostic detail.
    pub(crate) message: String,
}

/// SCC-level recursion analysis used by both diagnostics and extraction.
#[derive(Debug, Clone, Default)]
pub(crate) struct LogicRecursionAnalysis {
    /// Deterministic diagnostics for unsupported cycles.
    pub(crate) errors: Vec<LogicRecursionError>,
    /// All nodes discovered to be recursive (self-recursive or in a mutual SCC).
    pub(crate) recursive_members: HashSet<String>,
    /// Mutual-recursive SCC members accepted through the bounded first slice.
    pub(crate) supported_scc_members: HashSet<String>,
}

#[derive(Debug, Clone)]
pub(super) struct LogicRecursionNode {
    pub(super) full_path: String,
    pub(super) name: String,
    pub(super) params: Vec<String>,
    pub(super) param_sort_hints: Vec<Option<ExprSort>>,
    pub(super) mode: LogicMode,
    pub(super) is_trait_method: bool,
    pub(super) body: PureExpr,
    pub(super) body_text: String,
    pub(super) requires: Vec<PureExpr>,
    pub(super) ensures: Vec<PureExpr>,
    pub(super) raw_variants: Vec<String>,
    pub(super) parsed_variants: Vec<PureExpr>,
    pub(super) variant_parse_errors: Vec<String>,
    /// True when the logic function body could not be parsed into a PureExpr.
    /// Parse-failed nodes participate in call-graph construction via text scanning
    /// but lack structured call edges for argument analysis.
    pub(super) body_parse_failed: bool,
    /// Typed `DeepModel::deep_model` dispatch targets resolved from the
    /// implementing ADT's field types (see
    /// `LogicFunction::deep_model_dispatch_targets`). `Some(set)` lists the
    /// in-crate `<C as DeepModel>::deep_model` full-paths this body can
    /// actually dispatch into; an empty set means it only recurses into
    /// primitives/generics (genuinely non-recursive). `None` means the typed
    /// resolution did not apply (not a `deep_model` impl, or a unit-test node
    /// constructed without `tcx`) — consumers DEFAULT-REJECT on `None`.
    pub(super) deep_model_dispatch_targets: Option<HashSet<String>>,
}

/// Validate recursive logic-function structure.
///
/// Current rules:
/// - Direct recursion without `#[variant(...)]` is allowed (note emitted).
///   Creusot does not require `#[variant]` for structurally recursive logic fns.
/// - Mutual recursion is rejected unless the SCC satisfies the bounded
///   parsed-call integer-variant support slice.
pub(crate) fn validate_logic_fn_recursion(tcx: TyCtxt<'_>) -> Vec<LogicRecursionError> {
    analyze_logic_fn_recursion(tcx).errors
}

pub(crate) fn analyze_logic_fn_recursion(tcx: TyCtxt<'_>) -> LogicRecursionAnalysis {
    let logic_functions = find_logic_functions(tcx);
    let mut analysis = analyze_logic_fn_recursion_for_functions(&logic_functions);
    // Typed trait-bound recursion (Creusot "Illegal recursive trait"): a logic
    // method of a trait whose bound graph cycles back to itself can dispatch
    // into its own definition through the typing context (impl-trait argument,
    // trait/supertrait where-clause) — edges no body walk can see. These are
    // definition-level rejects; they need `tcx`, so they only join the
    // tcx-backed analysis entrypoint (the driver's fail-closed gate).
    for error in trait_bounds::collect_recursive_trait_bound_errors(tcx) {
        if !analysis.errors.iter().any(|existing| {
            existing.full_path == error.full_path && existing.message == error.message
        }) {
            analysis.errors.push(error);
        }
    }
    analysis.errors.sort_by(|a, b| {
        a.full_path
            .cmp(&b.full_path)
            .then_with(|| a.message.cmp(&b.message))
    });
    analysis
}

pub(crate) fn analyze_logic_fn_recursion_for_functions(
    logic_functions: &[LogicFunction],
) -> LogicRecursionAnalysis {
    let nodes = build_logic_recursion_nodes(logic_functions);
    analyze_logic_fn_recursion_nodes(&nodes)
}

fn build_logic_recursion_nodes(logic_functions: &[LogicFunction]) -> Vec<LogicRecursionNode> {
    logic_functions
        .iter()
        .filter_map(|logic_fn| {
            let (parsed_variants, variant_parse_errors) =
                parse_logic_variants(logic_fn.variants.iter(), &logic_fn.full_path);
            match to_logic_fn_def(logic_fn) {
                Some(mut parsed) => Some(LogicRecursionNode {
                    full_path: logic_fn.full_path.clone(),
                    name: logic_fn.name.clone(),
                    params: logic_fn.params.clone(),
                    param_sort_hints: logic_fn.param_sort_hints.clone(),
                    mode: logic_fn.mode,
                    is_trait_method: logic_fn.is_trait_method,
                    body: parsed.take_body(),
                    body_text: logic_fn.body_text.clone().unwrap_or_default(),
                    requires: parsed.take_requires(),
                    ensures: parsed.take_ensures(),
                    raw_variants: logic_fn.variants.clone(),
                    parsed_variants,
                    variant_parse_errors,
                    body_parse_failed: false,
                    deep_model_dispatch_targets: logic_fn.deep_model_dispatch_targets.clone(),
                }),
                None => {
                    // Body parse failure: create a minimal node so the function
                    // still participates in text-based call-graph construction and
                    // SCC detection. Without this, parse-failed logic functions
                    // silently escape recursion checking, creating false-accept
                    // soundness gaps (e.g., bug/1966.rs sneak/nonstrictly/nested).
                    let body_text = logic_fn.body_text.clone().unwrap_or_default();
                    if body_text.is_empty() {
                        return None;
                    }
                    Some(LogicRecursionNode {
                        full_path: logic_fn.full_path.clone(),
                        name: logic_fn.name.clone(),
                        params: logic_fn.params.clone(),
                        param_sort_hints: logic_fn.param_sort_hints.clone(),
                        mode: logic_fn.mode,
                        is_trait_method: logic_fn.is_trait_method,
                        // Use a dummy True body -- text-based scanning from
                        // body_text will still detect call references.
                        body: PureExpr::Bool(true),
                        body_text,
                        requires: vec![],
                        ensures: vec![],
                        raw_variants: logic_fn.variants.clone(),
                        parsed_variants,
                        variant_parse_errors,
                        body_parse_failed: true,
                        deep_model_dispatch_targets: logic_fn.deep_model_dispatch_targets.clone(),
                    })
                }
            }
        })
        .collect()
}

fn parse_logic_variants<'a>(
    variants: impl IntoIterator<Item = &'a String>,
    full_path: &str,
) -> (Vec<PureExpr>, Vec<String>) {
    let mut parsed = Vec::new();
    let mut errors = Vec::new();
    for variant in variants {
        match parse_contract(variant) {
            Ok(expr) => parsed.push(expr),
            Err(error) => errors.push(format!(
                "failed to parse #[variant(...)] '{}' for {}: {}",
                variant, full_path, error
            )),
        }
    }
    (parsed, errors)
}

fn analyze_logic_fn_recursion_nodes(nodes: &[LogicRecursionNode]) -> LogicRecursionAnalysis {
    if nodes.is_empty() {
        return LogicRecursionAnalysis::default();
    }

    let graph = build_logic_call_graph(nodes);
    let lookup = build_logic_name_lookup(nodes);
    let parsed_edges = collect_parsed_logic_call_edges(nodes, &lookup);
    let mut analysis = LogicRecursionAnalysis::default();

    for component in strongly_connected_components(&graph) {
        if component.len() > 1 {
            analysis
                .recursive_members
                .extend(component.iter().map(|&idx| nodes[idx].full_path.clone()));
            let mut cycle_paths: Vec<String> = component
                .iter()
                .map(|&idx| nodes[idx].full_path.clone())
                .collect();
            cycle_paths.sort();
            let cycle_desc = cycle_paths.join(", ");

            let mut missing_variants: Vec<String> = component
                .iter()
                .filter(|&&idx| nodes[idx].raw_variants.is_empty())
                .map(|&idx| nodes[idx].full_path.clone())
                .collect();
            missing_variants.sort();

            if !missing_variants.is_empty() {
                let missing_variant_desc = missing_variants.join(", ");
                for idx in component {
                    analysis.errors.push(LogicRecursionError {
                        full_path: nodes[idx].full_path.clone(),
                        message: format!(
                            "mutual recursion among logic functions without #[variant(...)] \
                             is not supported (cycle: {cycle_desc}; missing variant: \
                             {missing_variant_desc})"
                        ),
                    });
                }
                continue;
            }

            match validate_supported_mutual_recursion_scc(&component, nodes, &graph, &parsed_edges)
            {
                Ok(()) => {
                    for idx in component {
                        analysis
                            .supported_scc_members
                            .insert(nodes[idx].full_path.clone());
                    }
                }
                Err((edge, reason)) => {
                    for idx in component {
                        analysis.errors.push(LogicRecursionError {
                            full_path: nodes[idx].full_path.clone(),
                            message: format!(
                                "mutual recursion among logic functions is not yet supported \
                                 (cycle: {cycle_desc}; unsupported edge: {edge}; reason: {reason})"
                            ),
                        });
                    }
                }
            }
            continue;
        }

        let idx = component[0];
        if has_self_edge(&graph, idx) {
            analysis
                .recursive_members
                .insert(nodes[idx].full_path.clone());
            if nodes[idx].raw_variants.is_empty() {
                // SOUND structural-recursion acceptance (M4), mirroring Creusot
                // `terminates.rs:122-126` (`pearlite && is_structurally_recursive`
                // ⇒ forget the function is recursive). A single-node self-edge
                // whose body provably recurses on a STRICT SUBTERM of one fixed
                // argument on every self-call terminates structurally and needs
                // no `#[variant]`. Gated on a successfully-parsed body — a
                // parse-failed body cannot be analysed, so it falls through to
                // the conservative reject below (never accept on uncertainty).
                // The check is conservative: bug/1966 `me`/`nonstrictly`/
                // `nested`/`falso` all fail it (non-strict / same-arg / mutual /
                // zero-arg) and stay rejected.
                if !nodes[idx].body_parse_failed
                    && structural::is_structurally_recursive(&nodes[idx])
                {
                    // Termination guaranteed structurally; accept without proof.
                } else if nodes[idx].body_parse_failed {
                    analysis.errors.push(LogicRecursionError {
                        full_path: nodes[idx].full_path.clone(),
                        message: "self-recursive logic function with unparseable body requires \
                             #[variant(...)]: cannot verify termination without parsed body"
                            .to_string(),
                    });
                } else if has_conservative_open_self_trait_dispatch(idx, nodes, &parsed_edges)
                    || body_text_has_self_dispatch(&nodes[idx].body_text)
                {
                    analysis.errors.push(LogicRecursionError {
                        full_path: nodes[idx].full_path.clone(),
                        message: "self-dispatch through a trait default requires #[variant(...)]: \
                             cannot verify termination through dynamic trait dispatch"
                            .to_string(),
                    });
                } else if body_text_has_deep_model_dispatch(&nodes[idx]) {
                    analysis.errors.push(LogicRecursionError {
                        full_path: nodes[idx].full_path.clone(),
                        message: "recursive DeepModel dispatch through a container requires \
                             #[variant(...)]: cannot verify termination through the wrapper call"
                            .to_string(),
                    });
                } else if has_unconditional_non_progressing_self_recursion(
                    idx,
                    &nodes[idx],
                    &parsed_edges,
                ) {
                    // Check for unconditional self-recursion: if any self-call has
                    // no path conditions AND passes the exact same arguments (or no
                    // arguments), the function always recurses without progress and
                    // cannot terminate. This catches patterns like:
                    //   fn falso() { falso() }         -- zero-arg unconditional
                    //   fn me(self) { self.me() }       -- same-arg unconditional
                    //
                    // Functions that pass structurally different arguments (e.g.,
                    // `fn fib(n) { fib(n-1) + fib(n-2) }`) are allowed even without
                    // path conditions, since the argument may reach a base case in
                    // the domain. Creusot accepts this pattern for logic functions.
                    //
                    // Creusot rejects truly non-progressing recursion; trust-wp must
                    // too for soundness (#2686).
                    analysis.errors.push(LogicRecursionError {
                        full_path: nodes[idx].full_path.clone(),
                        message: "unconditional self-recursion without #[variant(...)]: \
                             function always calls itself with no decreasing argument"
                            .to_string(),
                    });
                } else {
                    // Conditional self-recursion without #[variant]: Creusot does
                    // not require #[variant] for structurally recursive logic fns.
                    // Ground instance evaluation handles these.
                    eprintln!(
                        "trust-wp: note: recursive logic function `{}` has no #[variant(...)]; \
                         recursion accepted without termination proof",
                        nodes[idx].full_path
                    );
                }
            } else {
                // #[variant(...)] is present. Try a solver-backed variant-decrease
                // obligation on the supported integer fragment (closes the
                // false-accept in terminates/incorrect_variant.rs where the text
                // heuristic accepted a variant that does not decrease). The proof
                // is only attempted when the variant AND every structured self-call
                // edge are inside the supported fragment; otherwise we fall back to
                // the prior text heuristic so legitimate should_succeed logic fns
                // with method/struct/Self::-dispatch/match variants are not
                // newly rejected (spans::quux/find_ptr_in_seq, bug/vcgen::set_max,
                // list_reversal_lasso::pigeon, ...).
                match try_prove_self_variant_decrease(idx, nodes, &graph, &parsed_edges) {
                    SelfVariantDecrease::Failed(reason) => {
                        analysis.errors.push(LogicRecursionError {
                            full_path: nodes[idx].full_path.clone(),
                            message: format!(
                                "self-recursive logic function variant does not strictly \
                                 decrease: {reason}"
                            ),
                        });
                    }
                    SelfVariantDecrease::Proven | SelfVariantDecrease::Unsupported => {
                        // Either proven to decrease, or outside the supported
                        // fragment. Preserve the prior negated-argument heuristic
                        // as a belt-and-suspenders reject (keeps bug/1204 `evil`
                        // rejected even though its `#[requires(false)]` makes the
                        // decrease obligation vacuously valid).
                        if body_text_has_negating_self_call(&nodes[idx]) {
                            analysis.errors.push(LogicRecursionError {
                                full_path: nodes[idx].full_path.clone(),
                                message: "self-recursive logic function calls itself with a \
                                     negated variant argument; variant decrease cannot be proven"
                                    .to_string(),
                            });
                        }
                    }
                }
            }
        }
    }

    add_trait_dispatch_text_pattern_errors(nodes, &mut analysis);
    add_deep_model_recursion_text_errors(nodes, &mut analysis);

    analysis.errors.sort_by(|a, b| {
        a.full_path
            .cmp(&b.full_path)
            .then_with(|| a.message.cmp(&b.message))
    });
    analysis
}

fn body_text_has_negating_self_call(node: &LogicRecursionNode) -> bool {
    let compact = node
        .body_text
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect::<String>();
    compact.contains(&format!("{}(-", node.name))
}

fn body_text_has_self_dispatch(body_text: &str) -> bool {
    compact_body_text(body_text).contains("Self::")
}

fn body_text_has_deep_model_dispatch(node: &LogicRecursionNode) -> bool {
    if node.name != "deep_model" || !compact_body_text(&node.body_text).contains(".deep_model()") {
        return false;
    }
    // SOUND typed gate (the spurious deep_model recursion-rejection bug): a
    // `.deep_model()` call only forms an in-crate recursion if its receiver
    // resolves to an in-crate `DeepModel` impl (a sibling/self concrete type),
    // not a primitive/generic field. When typed dispatch targets are resolved
    // from the implementing ADT's field types, an EMPTY set proves the body
    // only recurses into primitives/generics — genuinely non-recursive, so the
    // rejection must NOT fire (matching Creusot, which accepts these with zero
    // proof obligations). A non-empty set (e.g. bug/459's `Box<A>` resolving
    // back to `A`, or mixed.rs's `List`/`Expr` self-recursion through `Box`)
    // keeps the rejection. `None` (resolution did not apply) DEFAULT-REJECTs.
    if let Some(targets) = &node.deep_model_dispatch_targets {
        if targets.is_empty() {
            return false;
        }
    }
    // SOUND structural-recursion gate (M4): a recursive `deep_model` impl that
    // recurses on a STRICT SUBTERM of a single fixed argument on every self-call
    // is structurally terminating — Creusot accepts these via
    // `is_structurally_recursive` (terminates.rs:669) with zero proof
    // obligations. mixed.rs's `List`/`Expr` recurse via `(*tail).deep_model()`
    // (the `Deref`-unwrapped Self receiver IS a strict subterm of `self`), so
    // the rejection must NOT fire. bug/459's `*a.deep_model()` applies
    // `.deep_model()` to the BARE `Box<A>` binding (mutual recursion through the
    // wrapper's impl, NOT a same-type self-call) → `is_structurally_recursive`
    // returns false → it stays rejected. The check is conservative: any
    // uncertainty (non-strict, different arg per call, wrapper/mutual cycle)
    // yields false.
    if structural::is_structurally_recursive(node) {
        return false;
    }
    true
}

/// Reject logic functions named `deep_model` whose body dispatches via
/// `<receiver>.deep_model()` without a `#[variant(...)]`. The recursion may
/// be indirect through the container's `DeepModel` impl (e.g.,
/// `<A as DeepModel>::deep_model` calls `.deep_model()` on a `Box<A>` field,
/// which recursively calls back into `<A as DeepModel>::deep_model`), so the
/// call-graph cannot see the cycle structurally. This check fires
/// independently of detected self-edges to catch cases where text scanning
/// could not add the edge because the receiver is non-self
/// (creusot tests/should_fail/bug/459.rs).
fn add_deep_model_recursion_text_errors(
    nodes: &[LogicRecursionNode],
    analysis: &mut LogicRecursionAnalysis,
) {
    for node in nodes {
        if !body_text_has_deep_model_dispatch(node) {
            continue;
        }
        if !node.raw_variants.is_empty() {
            continue;
        }
        if analysis
            .errors
            .iter()
            .any(|error| error.full_path == node.full_path)
        {
            continue;
        }
        analysis.errors.push(LogicRecursionError {
            full_path: node.full_path.clone(),
            message: "recursive DeepModel dispatch through a container requires                  #[variant(...)]: cannot verify termination through the wrapper call"
                .to_string(),
        });
    }
}

fn add_trait_dispatch_text_pattern_errors(
    nodes: &[LogicRecursionNode],
    analysis: &mut LogicRecursionAnalysis,
) {
    let references = nodes
        .iter()
        .map(|node| {
            (
                node,
                collect_raw_logic_reference_names(node),
                compact_body_text(&node.body_text),
            )
        })
        .collect::<Vec<_>>();
    let trait_dispatch_participants = trait_dispatch_text_pattern_participants(&references);
    if !trait_dispatch_participants.is_empty() {
        push_text_pattern_errors(
            nodes,
            analysis,
            &trait_dispatch_participants,
            "trait method dispatch creates a mutual recursion cycle that cannot be resolved structurally",
        );
    }
}

fn has_conservative_open_self_trait_dispatch(
    node_idx: usize,
    nodes: &[LogicRecursionNode],
    parsed_edges: &[call_edges::LogicCallEdge],
) -> bool {
    let references = collect_raw_logic_reference_names(&nodes[node_idx]);
    parsed_edges.iter().any(|edge| {
        edge.caller_idx == node_idx
            && edge.callee_idx != node_idx
            && nodes[edge.callee_idx].is_trait_method
            && matches!(nodes[edge.callee_idx].mode, LogicMode::OpenSelf)
            && references_self_dispatch_to(&references, &nodes[edge.callee_idx].name)
    })
}

fn collect_raw_logic_reference_names(node: &LogicRecursionNode) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_logic_references(&node.body, &mut names);
    collect_logic_references_from_text(&node.body_text, &mut names);
    for req in &node.requires {
        collect_logic_references(req, &mut names);
    }
    for ens in &node.ensures {
        collect_logic_references(ens, &mut names);
    }
    names
}

fn references_self_dispatch_to(references: &HashSet<String>, name: &str) -> bool {
    references.iter().any(|reference| {
        reference
            .strip_prefix("Self::")
            .or_else(|| reference.strip_prefix("self::"))
            .is_some_and(|target| target == name)
    })
}

fn trait_dispatch_text_pattern_participants(
    references: &[(&LogicRecursionNode, HashSet<String>, String)],
) -> HashSet<String> {
    let mut participants = HashSet::new();
    let nodes = references
        .iter()
        .map(|(node, _, _)| (*node).clone())
        .collect::<Vec<_>>();
    let lookup = build_logic_name_lookup(&nodes);

    for (default_idx, (default_node, default_refs, _)) in references.iter().enumerate() {
        if !is_trait_dispatch_path(default_node) {
            continue;
        }

        for (bridge_idx, (bridge_node, bridge_refs, _)) in references.iter().enumerate() {
            if !node_references_node(default_refs, bridge_idx, bridge_node, &lookup) {
                continue;
            }

            for (impl_idx, (impl_node, impl_refs, _)) in references.iter().enumerate() {
                if !is_trait_dispatch_path(impl_node)
                    || default_idx == impl_idx
                    || !node_references_node(bridge_refs, impl_idx, impl_node, &lookup)
                    || !references_self_dispatch_to(impl_refs, &default_node.name)
                {
                    continue;
                }

                participants.insert(default_node.full_path.clone());
                participants.insert(bridge_node.full_path.clone());
                participants.insert(impl_node.full_path.clone());
            }
        }
    }

    participants
}

fn node_references_node(
    references: &HashSet<String>,
    target_idx: usize,
    target: &LogicRecursionNode,
    lookup: &LogicNameLookup,
) -> bool {
    references.iter().any(|reference| {
        resolve_logic_call_targets(reference, &lookup.full_path_to_idx, &lookup.name_to_indices)
            .contains(&target_idx)
            || qualified_trait_impl_reference_matches(reference, target)
    })
}

fn is_trait_dispatch_path(node: &LogicRecursionNode) -> bool {
    node.is_trait_method
        || (node.full_path.contains('<')
            && node.full_path.contains(" as ")
            && node.full_path.contains('>'))
        || (node.full_path.contains("<impl ")
            && node.full_path.contains(" for ")
            && node.full_path.contains('>'))
}

fn qualified_trait_impl_reference_matches(reference: &str, target: &LogicRecursionNode) -> bool {
    let Some((trait_name, method_name)) = qualified_trait_reference_parts(reference) else {
        return false;
    };
    target.name == method_name
        && target
            .full_path
            .contains(&format!("<impl {trait_name} for "))
        && target.full_path.ends_with(&format!("::{method_name}"))
}

fn qualified_trait_reference_parts(reference: &str) -> Option<(&str, &str)> {
    let reference = reference.strip_prefix('<')?;
    let (before_method, method_name) = reference.rsplit_once("::")?;
    let trait_start = before_method.find(" as ")? + " as ".len();
    let trait_end = before_method[trait_start..].find('>')? + trait_start;
    Some((&before_method[trait_start..trait_end], method_name))
}

fn push_text_pattern_errors(
    nodes: &[LogicRecursionNode],
    analysis: &mut LogicRecursionAnalysis,
    names: &HashSet<String>,
    message: &str,
) {
    for node in nodes.iter().filter(|node| names.contains(&node.full_path)) {
        push_pattern_error(node, analysis, message);
    }
}

fn push_pattern_error(
    node: &LogicRecursionNode,
    analysis: &mut LogicRecursionAnalysis,
    message: &str,
) {
    if analysis
        .errors
        .iter()
        .any(|error| error.full_path == node.full_path)
    {
        return;
    }
    analysis.errors.push(LogicRecursionError {
        full_path: node.full_path.clone(),
        message: message.to_string(),
    });
}

fn compact_body_text(body_text: &str) -> String {
    body_text.chars().filter(|ch| !ch.is_whitespace()).collect()
}

/// Does the (whitespace-compacted) body text contain a `self.<name>(...)`
/// method call? Used as the text-level fallback for self-named self-dispatch
/// detection so parse-failed bodies stay fail-closed. The preceding-character
/// guard prevents `myself.f(` / `x.herself.f(` from matching as `self.f(`.
fn compact_text_has_self_named_dispatch(body_text: &str, name: &str) -> bool {
    let compact = compact_body_text(body_text);
    let needle = format!("self.{name}(");
    let bytes = compact.as_bytes();
    let mut search_from = 0;
    while let Some(offset) = compact[search_from..].find(&needle) {
        let position = search_from + offset;
        let preceded_by_ident_char = position > 0 && {
            let previous = bytes[position - 1];
            previous.is_ascii_alphanumeric() || previous == b'_' || previous == b'.'
        };
        if !preceded_by_ident_char {
            return true;
        }
        search_from = position + 1;
    }
    false
}

/// Check if a self-recursive node has at least one unconditional, non-progressing
/// self-call.
///
/// A non-progressing self-call is one where:
/// - `path_conditions` are empty (call occurs on every execution path), AND
/// - Arguments are identical to the function's parameters (no structural decrease),
///   OR the function has no parameters.
///
/// This detects patterns like `fn f() { f() }` (zero-arg) and
/// `fn f(x) { f(x) }` (identity pass-through), but NOT patterns like
/// `fn fib(n) { fib(n-1) + fib(n-2) }` where arguments differ structurally.
///
/// Text-only edges are excluded since they may be false positives from
/// conservative text scanning.
fn has_unconditional_non_progressing_self_recursion(
    node_idx: usize,
    node: &LogicRecursionNode,
    parsed_edges: &[call_edges::LogicCallEdge],
) -> bool {
    parsed_edges.iter().any(|edge| {
        edge.caller_idx == node_idx
            && edge.callee_idx == node_idx
            && edge.path_conditions.is_empty()
            && !edge.recovered_from_text_only
            && args_are_identity_passthrough(&node.params, &edge.actual_args)
    })
}

/// Check if actual arguments are just identity pass-through of the formal parameters.
///
/// Returns true when:
/// - Both are empty (zero-arg function calling itself), OR
/// - Each actual arg is a `Var` whose name matches the corresponding formal param.
///
/// Returns false when arguments structurally differ from the parameters (e.g.,
/// `f(n-1)` vs param `n`), allowing the recursion to potentially terminate.
fn args_are_identity_passthrough(params: &[String], actual_args: &[PureExpr]) -> bool {
    if params.is_empty() && actual_args.is_empty() {
        return true;
    }
    if params.len() != actual_args.len() {
        return false;
    }
    params
        .iter()
        .zip(actual_args.iter())
        .all(|(param, arg)| matches!(arg, PureExpr::Var(name, _) if name == param))
}

#[cfg(test)]
fn detect_logic_fn_recursion_errors(nodes: &[LogicRecursionNode]) -> Vec<LogicRecursionError> {
    analyze_logic_fn_recursion_nodes(nodes).errors
}

#[cfg(test)]
#[path = "recursion_tests.rs"]
mod tests;
