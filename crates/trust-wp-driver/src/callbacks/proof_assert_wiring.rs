// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure wiring and enrichment passes for proof assertion verification.
//!
//! Extracted from `proof_assert_verify.rs` to keep each module under 500 LOC.
//! Handles Phase 8 (closure enrichment) of the proof_assert verification pipeline:
//! forall precondition instantiation, existential/forall closure enrichment,
//! obligation filtering, const substitution, trivial closure discharge,
//! capture info collection, and logic function mode scoping.

use std::{collections::HashMap, sync::Arc};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
use tracing::{debug, info};
use trust_wp_core::{
    closure::ClosureCaptureInfo,
    formula::{internal::tuple_lowering::tuple_logic_fn_arity, PureExpr},
    logic::LogicMode,
};
use trust_wp_driver::StdSpec;

use super::{
    closure_enrichment::{
        collect_closure_capture_infos, collect_trivial_closure_receivers,
        enrich_existentials_with_closure_ensures, enrich_forall_goals_with_closure_ensures,
        instantiate_forall_precondition_rules, rewrite_trivial_closure_precondition_goal,
        synthesized_ensures_from_capture_infos,
    },
    logic_fn_scope::scope_logic_fn_modes,
    proof_assert_extract::is_deref_precondition,
    type_invariants::build_closure_capture_invariant_requires,
};

/// Result of closure wiring and enrichment passes.
pub(super) struct ClosureWiringResult {
    pub(super) ensures: Vec<PureExpr>,
    pub(super) closure_capture_infos: Vec<ClosureCaptureInfo>,
    pub(super) mode_overrides: Option<Vec<LogicMode>>,
}

/// Shared context for closure wiring passes (#2657).
///
/// Bundles the read-only configuration and spec data that is constant
/// across a single proof_assert verification, keeping
/// `apply_closure_wiring` under clippy's argument threshold.
pub(super) struct ClosureWiringContext<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) containing_fn: LocalDefId,
    pub(super) owner_local: LocalDefId,
    pub(super) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) const_item_substitutions: &'a HashMap<String, PureExpr>,
    pub(super) logic_fn_defs: &'a [trust_wp_core::logic::LogicFnDef],
    pub(super) type_invariant_defs: &'a [trust_wp_core::logic::TypeInvariantDef],
    pub(super) verbose: bool,
    pub(super) body_arg_names: &'a [String],
    pub(super) fn_path: &'a str,
}

/// Apply closure wiring and enrichment passes to finalize ensures.
///
/// Handles: forall precondition instantiation, existential closure enrichment,
/// obligation filtering (deref discharge), const substitution in ensures/preconditions,
/// trivial closure precondition discharge, forall-goal closure enrichment, and
/// closure capture info collection.
pub(super) fn apply_closure_wiring(
    ctx: &ClosureWiringContext<'_, '_>,
    preconditions: &mut Vec<PureExpr>,
    assertion: PureExpr,
    call_obligations: &[PureExpr],
) -> ClosureWiringResult {
    let tcx = ctx.tcx;
    let containing_fn = ctx.containing_fn;
    let owner_local = ctx.owner_local;
    let user_specs = ctx.user_specs;
    let const_item_substitutions = ctx.const_item_substitutions;
    let logic_fn_defs = ctx.logic_fn_defs;
    let type_invariant_defs = ctx.type_invariant_defs;
    let verbose = ctx.verbose;
    let body_arg_names = ctx.body_arg_names;
    let fn_path = ctx.fn_path;
    let grounded_forall_preconditions = instantiate_forall_precondition_rules(preconditions);
    if verbose && grounded_forall_preconditions > 0 {
        debug!(
            "trust-wp:   (proof_assert: {grounded_forall_preconditions} grounded precondition assumption(s) from forall rules)",
        );
    }

    // Collect closure capture infos early so synthesized ensures are available
    // for enrichment (#2151 Phase 3). Body inlining requires trait_specs/extern_specs
    // for MIR extraction. proof_assert closures are typically simple enough that the
    // user_specs-only path suffices; pass empty maps as fallback.
    let empty_trait_specs = HashMap::new();
    let empty_extern_specs = HashMap::new();
    let mut closure_capture_infos = collect_closure_capture_infos(
        tcx,
        owner_local,
        user_specs,
        &empty_trait_specs,
        &empty_extern_specs,
    );
    if containing_fn != owner_local
        && tcx.def_kind(containing_fn.to_def_id()) == rustc_hir::def::DefKind::Closure
    {
        for info in collect_closure_capture_infos(
            tcx,
            containing_fn,
            user_specs,
            &empty_trait_specs,
            &empty_extern_specs,
        ) {
            merge_inner_closure_capture_info(&mut closure_capture_infos, info);
        }
    }
    if verbose && !closure_capture_infos.is_empty() {
        debug!(
            "trust-wp:   (proof_assert: {} closure capture info(s) for structural sort registration)",
            closure_capture_infos.len()
        );
    }

    // Extract synthesized ensures from capture infos for unannotated FnMut closures.
    if verbose {
        for ci in &closure_capture_infos {
            debug!(
                "trust-wp:   (proof_assert: capture_info def_id={} ensures_exprs={:?} captures={})",
                ci.def_id(),
                ci.ensures_exprs().map(<[PureExpr]>::len),
                ci.captures().len()
            );
        }
    }
    let synth_ensures = synthesized_ensures_from_capture_infos(&closure_capture_infos);
    if verbose && !synth_ensures.is_empty() {
        debug!(
            "trust-wp:   (proof_assert: {} synthesized ensures entry/entries from body effect analysis)",
            synth_ensures.len()
        );
        for entry in &synth_ensures {
            debug!(
                "trust-wp:   (proof_assert: synth ensures receiver={} bindings={:?} ensures_count={})",
                entry.receiver_name,
                entry.capture_bindings,
                entry.ensures_exprs.len()
            );
        }
    }
    let capture_inv_requires =
        build_closure_capture_invariant_requires(&closure_capture_infos, type_invariant_defs);
    if verbose && !capture_inv_requires.is_empty() {
        debug!(
            "trust-wp:   (proof_assert: {} closure capture invariant precondition(s) injected)",
            capture_inv_requires.len()
        );
    }
    preconditions.extend(capture_inv_requires);

    if verbose {
        debug!(
            "trust-wp:   (proof_assert: {} precondition(s) before enrichment)",
            preconditions.len()
        );
        for (i, pre) in preconditions.iter().enumerate() {
            let dbg = format!("{pre:?}");
            if dbg.contains("postcondition") {
                debug!(
                    "trust-wp:   (proof_assert: precondition[{i}] contains postcondition: {dbg:.200})"
                );
            }
        }
    }

    // Mirror contract verification closure enrichment in proof_assert path (#1180):
    // - enrich existential assumptions with grounded closure ensures
    // - enrich forall proof goals with grounded closure ensures
    let closure_enrichment_count = enrich_existentials_with_closure_ensures(
        tcx,
        containing_fn,
        user_specs,
        preconditions.as_mut_slice(),
        &synth_ensures,
    );
    if verbose && closure_enrichment_count > 0 {
        eprintln!(
            "trust-wp:   (proof_assert: {closure_enrichment_count} closure existential enrichment(s) applied)",
        );
        info!(
            "trust-wp:   (proof_assert: {closure_enrichment_count} closure existential enrichment(s) applied)",
        );
    }

    // Build ensures: obligations must be proved AND assertion must hold.
    // Filter out deref/deref_mut precondition obligations -- these are always
    // satisfiable for value types (tuples, primitives) used in ghost blocks.
    // The solver has no axiom for T::deref.precondition / T::deref_mut.precondition
    // so leaving them as obligations makes the proof impossible. (#1572)
    let assertion =
        advance_single_capture_fnonce_assertion(assertion, preconditions, &synth_ensures);

    let mut ensures_vec: Vec<PureExpr> = call_obligations
        .iter()
        .filter(|ob| !is_deref_precondition(ob))
        .cloned()
        .collect();
    let discharged_deref = call_obligations.len() - ensures_vec.len();
    if verbose && discharged_deref > 0 {
        debug!(
            "trust-wp:   (proof_assert: {discharged_deref} deref precondition obligation(s) discharged)",
        );
    }
    ensures_vec.push(assertion);

    // Substitute named const items in preconditions too. (#1588)
    if !const_item_substitutions.is_empty() {
        for expr in preconditions.iter_mut() {
            *expr = expr.substitute(const_item_substitutions);
        }
        for expr in &mut ensures_vec {
            *expr = expr.substitute(const_item_substitutions);
        }
    }

    // Concrete closures without explicit requires have vacuous preconditions.
    // Keep explicit closure requires as obligations.
    let trivial_closure_receivers =
        collect_trivial_closure_receivers(containing_fn, body_arg_names, user_specs);
    debug!(
        "trust-wp:   (proof_assert debug trivial closure receivers: {trivial_closure_receivers:?})"
    );
    if !trivial_closure_receivers.is_empty() {
        let mut rewritten = 0usize;
        for goal in &mut ensures_vec {
            if rewrite_trivial_closure_precondition_goal(goal, &trivial_closure_receivers) {
                rewritten += 1;
            }
        }
        if verbose && rewritten > 0 {
            debug!(
                "trust-wp:   (proof_assert: {rewritten} trivial closure precondition obligation(s) discharged)",
            );
        }
    }

    let closure_forall_enrichment_count =
        enrich_forall_goals_with_closure_ensures(tcx, containing_fn, user_specs, &mut ensures_vec);
    if verbose && closure_forall_enrichment_count > 0 {
        eprintln!(
            "trust-wp:   (proof_assert: {closure_forall_enrichment_count} closure forall-goal enrichment(s) applied)",
        );
        info!(
            "trust-wp:   (proof_assert: {closure_forall_enrichment_count} closure forall-goal enrichment(s) applied)",
        );
    }

    // Scope logic function modes per containing function's module (#746 Gap 1).
    // Without this, Default-mode logic functions would unconditionally expose
    // axiom bodies regardless of module boundaries, diverging from the contract
    // verification path (verification.rs:685).
    let mode_overrides = if logic_fn_defs
        .iter()
        .any(|lf| matches!(lf.mode(), LogicMode::OpenSelf | LogicMode::Default))
    {
        Some(scope_logic_fn_modes(logic_fn_defs, fn_path))
    } else {
        None
    };

    ClosureWiringResult {
        ensures: ensures_vec,
        closure_capture_infos,
        mode_overrides,
    }
}

/// Merge a closure capture info collected from the inner closure's MIR into the
/// list collected from the outer (typeck-root) MIR.
///
/// When a `proof_assert` is inside a closure, both the outer-fn collection and
/// the inner-closure collection produce an entry for the same `def_id`:
///
/// - **Outer** (`collect_closure_capture_infos(owner_local=f)`): the MIR loop
///   over `StatementKind::Assign(Closure)` records the caller-side variable name
///   the closure was bound to (e.g. `Some("clos")`).
/// - **Inner** (`collect_closure_capture_infos(containing_fn=clos)`): when
///   `parent_local_def_id` is itself a closure, the seeded "current closure"
///   entry uses `param_name = Some("self")` (the body-side name).
///
/// For closure-internal `proof_assert!` verification, bootstrap sort registration
/// uses `info.param_name()` to call `record_source_sort(param_name, closure_sort)`
/// against the encoder's `ClosureEnv_*` Datatype. Recording under `"clos"` only
/// leaves `self` to fall back to `Uninterpreted("Tuple1")` via usage-based
/// tuple-arity inference (closures/10_tyinv: `self.0`, `self.1` projections).
///
/// This helper prefers the "self"-tagged entry when both exist for the same
/// `def_id`, so the encoder receives the body-side `self` sort registration
/// it needs for native `closure_capture_<suffix>_N` selector routing. The
/// change tightens sort information (`Datatype` is strictly more precise than
/// `Uninterpreted("Tuple1")`), so soundness is monotonic. (Wave 20A blocker;
/// Phase 3 B4)
fn merge_inner_closure_capture_info(
    existing_infos: &mut Vec<ClosureCaptureInfo>,
    incoming: ClosureCaptureInfo,
) {
    if let Some(existing_pos) = existing_infos
        .iter()
        .position(|existing| existing.def_id() == incoming.def_id())
    {
        let prefer_new = incoming.param_name() == Some("self")
            && existing_infos[existing_pos].param_name() != Some("self");
        if prefer_new {
            existing_infos[existing_pos] = incoming;
        }
    } else {
        existing_infos.push(incoming);
    }
}

fn advance_single_capture_fnonce_assertion(
    assertion: PureExpr,
    preconditions: &[PureExpr],
    synth_ensures: &[super::closure_enrichment::ClosureEnsuresEntry],
) -> PureExpr {
    let Some(capture_name) = single_synthesized_capture_name(synth_ensures) else {
        return assertion;
    };

    let mut latest = None;
    for precondition in preconditions {
        collect_latest_fnonce_capture_state(precondition, &capture_name, &mut latest);
    }
    let Some(latest_expr) = latest else {
        return assertion;
    };

    rewrite_final_capture_to_latest(assertion, &capture_name, &latest_expr)
}

fn single_synthesized_capture_name(
    synth_ensures: &[super::closure_enrichment::ClosureEnsuresEntry],
) -> Option<String> {
    let mut entries = synth_ensures
        .iter()
        .filter(|entry| entry.capture_bindings.len() == 1);
    let entry = entries.next()?;
    if entries.next().is_some() {
        return None;
    }
    Some(entry.capture_bindings[0].1.clone())
}

fn collect_latest_fnonce_capture_state(
    expr: &PureExpr,
    capture_name: &str,
    latest: &mut Option<PureExpr>,
) {
    match expr {
        // `postcondition_once` (FnOnce) and `postcondition_mut` (FnMut chains,
        // e.g. `call_fnmut`'s `exists<st1, st2, r> f.postcondition_mut(...) &&
        // st1.postcondition_mut(...) && resolve(st2)`) both advance the
        // caller-visible closure state past the receiver's prophecy layer.
        // For FnMut the receiver here is the call-site PRE-state env
        // (`tuple1(^..^x)` at depth d); the enriched ensures tether the
        // concrete final value at the post-state layer d+1, so the deepest
        // post-state across all call assumptions is the resolved final the
        // proof_assert goal must read (closures/07 test_fnmut2). Only fires
        // for a concrete single-capture tuple env whose sole field is a pure
        // Final-tower over the synthesized capture — opaque receivers
        // (`call_N`) and mixed expressions are ignored.
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if (method == "postcondition_once" && args.len() >= 2)
            || (method == "postcondition_mut" && args.len() == 3) =>
        {
            let post_state = super::closure_enrichment::final_receiver_state_expr(receiver);
            if let Some(candidate) = tuple1_capture_expr(&post_state) {
                update_latest_final_capture(candidate, capture_name, latest);
            }
        }
        PureExpr::BinOp(left, _, right) => {
            collect_latest_fnonce_capture_state(left, capture_name, latest);
            collect_latest_fnonce_capture_state(right, capture_name, latest);
        }
        PureExpr::Exists { body, .. } | PureExpr::Forall { body, .. } => {
            collect_latest_fnonce_capture_state(body, capture_name, latest);
        }
        _ => {}
    }
}

fn tuple1_capture_expr(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    if tuple_logic_fn_arity(name) == Some(1) && args.len() == 1 {
        args.first()
    } else {
        None
    }
}

fn update_latest_final_capture(
    candidate: &PureExpr,
    capture_name: &str,
    latest: &mut Option<PureExpr>,
) {
    let Some(candidate_depth) = final_depth_for_capture(candidate, capture_name) else {
        return;
    };
    let current_depth = latest
        .as_ref()
        .and_then(|expr| final_depth_for_capture(expr, capture_name))
        .unwrap_or(0);
    if candidate_depth > current_depth {
        *latest = Some(candidate.clone());
    }
}

fn rewrite_final_capture_to_latest(
    expr: PureExpr,
    capture_name: &str,
    latest_expr: &PureExpr,
) -> PureExpr {
    match expr {
        PureExpr::Final(inner) => {
            if let Some(current_depth) =
                final_depth_for_capture(&PureExpr::Final(inner.clone()), capture_name)
            {
                if final_depth_for_capture(latest_expr, capture_name).unwrap_or(0) > current_depth {
                    return latest_expr.clone();
                }
            }
            PureExpr::Final(Arc::new(rewrite_final_capture_to_latest(
                Arc::unwrap_or_clone(inner),
                capture_name,
                latest_expr,
            )))
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(rewrite_final_capture_to_latest(
                Arc::unwrap_or_clone(left),
                capture_name,
                latest_expr,
            )),
            op,
            Arc::new(rewrite_final_capture_to_latest(
                Arc::unwrap_or_clone(right),
                capture_name,
                latest_expr,
            )),
        ),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(rewrite_final_capture_to_latest(
                Arc::unwrap_or_clone(receiver),
                capture_name,
                latest_expr,
            )),
            method,
            args: args
                .into_iter()
                .map(|arg| rewrite_final_capture_to_latest(arg, capture_name, latest_expr))
                .collect(),
        },
        other => other,
    }
}

fn final_depth_for_capture(expr: &PureExpr, capture_name: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut current = expr;
    while let PureExpr::Final(inner) = current {
        depth += 1;
        current = inner;
    }
    match current {
        PureExpr::Var(name, _) if name == capture_name => Some(depth),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use trust_wp_core::formula::{BinOp, PureExpr};

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn final_n(mut expr: PureExpr, n: usize) -> PureExpr {
        for _ in 0..n {
            expr = PureExpr::Final(Arc::new(expr));
        }
        expr
    }

    fn tuple1(arg: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple1".to_string(),
            args: vec![arg],
        }
    }

    #[test]
    fn advances_single_capture_fnonce_assertion_to_latest_post_state() {
        let assertion = PureExpr::BinOp(
            Arc::new(final_n(var("x"), 2)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(100002)),
        );
        let preconditions = vec![
            PureExpr::MethodCall {
                receiver: Arc::new(tuple1(final_n(var("x"), 2))),
                method: "postcondition_once".to_string(),
                args: vec![tuple1(PureExpr::Bool(true)), PureExpr::Int(5)],
            },
            PureExpr::MethodCall {
                receiver: Arc::new(tuple1(final_n(var("x"), 3))),
                method: "postcondition_once".to_string(),
                args: vec![tuple1(PureExpr::Bool(true)), PureExpr::Int(5)],
            },
        ];
        let synth_ensures = vec![super::super::closure_enrichment::ClosureEnsuresEntry {
            receiver_name: "c".to_string(),
            param_names: vec![],
            capture_bindings: vec![(0, "x".to_string())],
            ensures_exprs: vec![],
        }];

        let rewritten =
            advance_single_capture_fnonce_assertion(assertion, &preconditions, &synth_ensures);

        assert!(matches!(
            rewritten,
            PureExpr::BinOp(left, BinOp::Eq, _) if *left == final_n(var("x"), 4)
        ));
    }

    /// When the outer-fn collection records a closure with the caller-side
    /// `param_name` (e.g., `Some("clos")`) and the inner-closure collection
    /// records the same closure with `param_name = Some("self")`, the merge
    /// must promote the `"self"`-tagged entry. Without this promotion, the ay
    /// bootstrap sort plan registers the caller-side variable as the closure
    /// env Datatype and leaves `self` to collapse to `Tuple1` via
    /// usage-based tuple-arity inference for `self.N` projections inside the
    /// closure's `proof_assert!` (closures/10_tyinv; Wave 20A blocker).
    #[test]
    fn merge_inner_closure_capture_info_promotes_self_param_name_over_caller_name() {
        let caller_entry = ClosureCaptureInfo::new("closure_def_id_42".to_string(), Vec::new())
            .with_param_name(Some("clos".to_string()));
        let mut infos = vec![caller_entry];
        let inner_entry = ClosureCaptureInfo::new("closure_def_id_42".to_string(), Vec::new())
            .with_param_name(Some("self".to_string()));

        merge_inner_closure_capture_info(&mut infos, inner_entry);

        assert_eq!(infos.len(), 1, "merge must not duplicate the same def_id");
        assert_eq!(
            infos[0].param_name(),
            Some("self"),
            "inner-closure `self` entry must replace the caller-side name so bootstrap \
             registers the closure env Datatype against `self` (#closures/10_tyinv)",
        );
    }

    /// Sibling closures discovered in the outer fn's MIR (`clos`, `clos2`, ...)
    /// keep their caller-side names — only the def_id matching the
    /// containing closure should ever flip to `"self"`. Verify the helper
    /// does not regress sibling entries.
    #[test]
    fn merge_inner_closure_capture_info_appends_distinct_def_ids() {
        let sibling = ClosureCaptureInfo::new("closure_def_id_sibling".to_string(), Vec::new())
            .with_param_name(Some("clos2".to_string()));
        let mut infos =
            vec![
                ClosureCaptureInfo::new("closure_def_id_self".to_string(), Vec::new())
                    .with_param_name(Some("self".to_string())),
            ];

        merge_inner_closure_capture_info(&mut infos, sibling);

        assert_eq!(infos.len(), 2, "distinct def_ids must both be retained");
        assert_eq!(infos[0].param_name(), Some("self"));
        assert_eq!(infos[1].param_name(), Some("clos2"));
    }

    /// When the inner entry has a non-"self" name (which should not normally
    /// happen, but we want a defensive bound on the helper), do not replace
    /// an existing entry. This preserves the prior semantics for non-Wave-20A
    /// paths.
    #[test]
    fn merge_inner_closure_capture_info_keeps_existing_for_non_self_incoming() {
        let mut infos = vec![
            ClosureCaptureInfo::new("closure_def_id_42".to_string(), Vec::new())
                .with_param_name(Some("clos".to_string())),
        ];
        let incoming = ClosureCaptureInfo::new("closure_def_id_42".to_string(), Vec::new())
            .with_param_name(Some("other".to_string()));

        merge_inner_closure_capture_info(&mut infos, incoming);

        assert_eq!(infos.len(), 1);
        assert_eq!(
            infos[0].param_name(),
            Some("clos"),
            "non-self incoming must not replace the existing caller-side entry",
        );
    }
}
