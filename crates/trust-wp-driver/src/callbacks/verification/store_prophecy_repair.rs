// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Branch-scoped superseding of stale prophecy pins for nested `&mut` params.
//!
//! When a spec'd mutating call (e.g. `mem::take(self_)`) is applied through a
//! temporary reborrow of a nested `&mut &mut T` parameter, its `^dest`-style
//! ensures clauses are instantiated with `dest := self_`, binding the callee's
//! *call-scoped* prophecy (the reborrow expires right after the call) to the
//! *function-scoped* prophecy `^self_`. That is only correct when the call is
//! the last mutation of `*self_`. If a later MIR deref-store `*self_ = v`
//! executes on some path, the function-exit resolution on that path is
//! `^self_ == v` — the unconditional pin (e.g. `(^self_)@ == Seq::empty()`
//! from `mem::take`'s specialized `Default` postcondition) is simply FALSE
//! there, killing every postcondition arm that needs the stored value
//! (take_first_mut class).
//!
//! This pass repairs the premise set from the extracted body structure:
//!
//! 1. It locates the (single) branch-scoped store fact
//!    `LetAssume { self_ == <rhs>, .. }` inside `result_expr` and derives the
//!    store's branch guard from the enclosing `Ite` conditions.
//! 2. It rewrites each unconditional `(^self_)…`-pin call assumption `P` into
//!    `Ite(guard, <last-state resolution>, P)`: on the store branch the
//!    prophecy resolves from the LAST state (`(^self_)@ == <rhs>@`, and
//!    `(^^self_)@ == (^<rhs>)@` when a distinct final-side symbol for the
//!    stored borrow exists); on all other branches the original call-scoped
//!    pin still holds (nothing superseded it).
//! 3. Fix for the `(*rem)@`/`(^rem)@` conflation: when the stored value is a
//!    payload projection of a `Match` call-assumption binding (e.g. `rem` from
//!    `split_first_mut`'s spec), the match-arm encoder collapses temporal
//!    wrappers on binder vars to the payload projection term, making
//!    `(^rem)@` and `(*rem)@` the SAME symbol (an over-constraint and a lost
//!    final side). This pass substitutes `Final(Var("rem"))` in that arm with
//!    a fresh function-scoped constant and uses the same constant as the
//!    final side of the store resolution, restoring the distinct-final-symbol
//!    linkage.
//!
//! Soundness:
//! - Guarding an existing pin (`P → Ite(guard, X, P)`) only *weakens* it on
//!   the store branch; on non-store branches the premise is unchanged.
//! - The added store-branch facts are the RustHorn last-state prophecy
//!   resolution: the guarded branch's final store to `*self_` is `<rhs>`
//!   (the pass requires exactly ONE store fact for the param in the body, so
//!   nothing later supersedes it), hence `^self_ == <rhs>` on that branch.
//! - The raw store equality `self_ == <rhs>` (which incorrectly pins the
//!   ENTRY carrier — `self_` is aliased to `self__current` — and is dropped
//!   as an ill-sorted `__trust_wp_coerce_*` constant today) is neutralized to
//!   `true`; removing an assumption is always sound.
//! - The fresh `Final(binding)` constant is unconstrained except for the
//!   match-arm facts that previously over-constrained the conflated symbol;
//!   naming an unconstrained value cannot enable a proof that was not
//!   semantically valid.
//!
//! The pass is tightly gated: it fires only for parameters of nested
//! `&mut &mut` type that have BOTH an unconditional `^param` view pin in
//! `call_assumptions` AND exactly one branch-scoped deref-store fact in
//! `result_expr`. Functions without that full pattern are untouched.

use std::sync::Arc;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Mutability, TyCtxt, TyKind};
use tracing::trace;
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_index, tuple_field_logic_fn_name},
    BinOp, Pattern, PureExpr, UnOp,
};

use super::super::parsing::ParsedContract;

/// Entry point: repair superseded prophecy pins for all nested `&mut &mut`
/// parameters of the contract.
pub(super) fn repair_superseded_prophecy_pins(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    parsed: &mut ParsedContract,
) {
    let nested_params = nested_mut_ref_param_names(tcx, def_id, &parsed.arg_names);
    if nested_params.is_empty() {
        return;
    }
    let Some(result_expr) = parsed.result_expr.clone() else {
        return;
    };

    for param in nested_params {
        // 1. Exactly one branch-scoped deref-store fact for this param.
        let mut stores = Vec::new();
        collect_param_store_assumes(&result_expr, &param, &mut Vec::new(), &mut stores);
        let [(guard_path, store_rhs)] = stores.as_slice() else {
            continue;
        };
        if guard_path.is_empty() {
            // Unconditional store: out of scope for this pass (the pin
            // machinery for straight-line stores is handled elsewhere).
            continue;
        }
        // The stored value must not itself depend on the param's symbols.
        if store_rhs.any_free_var(|name, _| name == param) {
            continue;
        }

        // 2. Unconditional `View(Final^k(param)) == <closed>` pins.
        let pin1_idx = find_unconditional_pin(&parsed.call_assumptions, &param, 1);
        let pin2_idx = find_unconditional_pin(&parsed.call_assumptions, &param, 2);
        if pin1_idx.is_none() && pin2_idx.is_none() {
            continue;
        }

        let guard = guard_expr(guard_path);

        // 3. Distinct current/final-side symbols for the stored borrow (fix
        //    for the `(*rem)@`/`(^rem)@` binder conflation, and for the
        //    placeholder-vs-native selector UF mismatch on the current side),
        //    when derivable.
        let canonical = canonicalize_stored_borrow_sides(&mut parsed.call_assumptions, store_rhs);
        if canonical.current.is_some() || canonical.final_side.is_some() {
            // Mirror the binder substitution in the pre-loop copy so the
            // loop-obligation path sees consistent symbols.
            let _ =
                canonicalize_stored_borrow_sides(&mut parsed.pre_loop_call_assumptions, store_rhs);
        }

        if let Some(idx) = pin1_idx {
            let current_rhs = canonical
                .current
                .clone()
                .unwrap_or_else(|| PureExpr::View(Arc::new(store_rhs.clone())));
            let superseding = PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                    PureExpr::Var(param.clone(), None),
                ))))),
                BinOp::Eq,
                Arc::new(current_rhs),
            );
            rewrite_pin_in_place(
                &mut parsed.call_assumptions,
                &mut parsed.pre_loop_call_assumptions,
                idx,
                &guard,
                superseding,
            );
        }
        if let Some(idx) = pin2_idx {
            let superseding = match &canonical.final_side {
                Some(final_view) => PureExpr::BinOp(
                    Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                        PureExpr::Final(Arc::new(PureExpr::Var(param.clone(), None))),
                    ))))),
                    BinOp::Eq,
                    Arc::new(final_view.clone()),
                ),
                // No distinct final-side symbol derivable: just descope the
                // stale pin on the store branch (sound weakening).
                None => PureExpr::Bool(true),
            };
            rewrite_pin_in_place(
                &mut parsed.call_assumptions,
                &mut parsed.pre_loop_call_assumptions,
                idx,
                &guard,
                superseding,
            );
        }

        // F1 facts (guarded on the non-store side): value-level
        // `X == Seq::empty()` pins entailed by the nullary match arm.
        for fact in &canonical.nullary_arm_empty_facts {
            let guarded = PureExpr::Ite(
                Arc::new(guard.clone()),
                Arc::new(PureExpr::Bool(true)),
                Arc::new(fact.clone()),
            );
            parsed.call_assumptions.push(guarded.clone());
            parsed.pre_loop_call_assumptions.push(guarded);
        }

        // Sibling payload bridges (guarded): connect the match-arm's
        // native-selector facts to the goal's placeholder-selector chain.
        for (fresh_var, projection) in &canonical.sibling_bridges {
            let bridge = PureExpr::Ite(
                Arc::new(guard.clone()),
                Arc::new(PureExpr::BinOp(
                    Arc::new(fresh_var.clone()),
                    BinOp::Eq,
                    Arc::new(projection.clone()),
                )),
                Arc::new(PureExpr::Bool(true)),
            );
            parsed.call_assumptions.push(bridge.clone());
            parsed.pre_loop_call_assumptions.push(bridge);
        }

        // 4. Neutralize the raw (ill-sorted, entry-pinning) store equality.
        if let Some(expr) = parsed.result_expr.take() {
            parsed.result_expr = Some(neutralize_store_assume(&expr, &param));
        }
        if let Some(spanned) = parsed.result_expr_spanned.as_mut() {
            spanned.expr = neutralize_store_assume(&spanned.expr, &param);
        }

        trace!(
            param = %param,
            had_current_pin = pin1_idx.is_some(),
            had_final_pin = pin2_idx.is_some(),
            distinct_current_symbol = canonical.current.is_some(),
            distinct_final_symbol = canonical.final_side.is_some(),
            "branch-scoped store supersedes call-scoped prophecy pins"
        );
    }
}

/// Names of parameters with nested `&mut &mut _` type.
fn nested_mut_ref_param_names(tcx: TyCtxt<'_>, def_id: DefId, arg_names: &[String]) -> Vec<String> {
    // Closures don't have fn_sig(); their parameters are captures.
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return Vec::new();
    }
    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip();
    let sig = tcx.liberate_late_bound_regions(def_id, sig);
    sig.inputs()
        .iter()
        .zip(arg_names)
        .filter_map(|(ty, name)| match ty.kind() {
            TyKind::Ref(_, inner, Mutability::Mut)
                if matches!(inner.kind(), TyKind::Ref(_, _, Mutability::Mut)) =>
            {
                Some(name.clone())
            }
            _ => None,
        })
        .collect()
}

/// Walk the `result_expr` spine collecting branch-scoped store facts
/// `LetAssume { param == <rhs>, .. }` together with their `Ite` guard paths.
///
/// Only descends through `Ite` arms and `LetAssume` bodies: store facts are
/// recorded on that spine by `wrap_projected_facts`. `Let`/`Match` nodes bind
/// variables, so conditions below them cannot be lifted to function scope —
/// the walk stops there (conservative: the pass simply won't fire).
fn collect_param_store_assumes(
    expr: &PureExpr,
    param: &str,
    path: &mut Vec<(PureExpr, bool)>,
    out: &mut Vec<(Vec<(PureExpr, bool)>, PureExpr)>,
) {
    match expr {
        PureExpr::Ite(cond, then_expr, else_expr) => {
            path.push((cond.as_ref().clone(), true));
            collect_param_store_assumes(then_expr, param, path, out);
            path.pop();
            path.push((cond.as_ref().clone(), false));
            collect_param_store_assumes(else_expr, param, path, out);
            path.pop();
        }
        PureExpr::LetAssume { assumption, body } => {
            if let Some(rhs) = param_store_rhs(assumption, param) {
                out.push((path.clone(), rhs));
            }
            collect_param_store_assumes(body, param, path, out);
        }
        _ => {}
    }
}

/// If `assumption` is a store fact `param == <rhs>` (or `*param == <rhs>`),
/// return the stored value.
fn param_store_rhs(assumption: &PureExpr, param: &str) -> Option<PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = assumption else {
        return None;
    };
    let lhs_is_param_store = match lhs.as_ref() {
        PureExpr::Var(name, _) => name == param,
        PureExpr::Deref(inner) => {
            matches!(inner.as_ref(), PureExpr::Var(name, _) if name == param)
        }
        _ => false,
    };
    lhs_is_param_store.then(|| rhs.as_ref().clone())
}

/// Find the single top-level call assumption `View(Final^depth(param)) == X`
/// with `X` closed w.r.t. the param and `result`. Returns `None` when absent
/// or ambiguous (more than one pin of the same depth — bail out).
fn find_unconditional_pin(assumptions: &[PureExpr], param: &str, depth: usize) -> Option<usize> {
    let mut found = None;
    for (idx, assumption) in assumptions.iter().enumerate() {
        if is_final_view_pin(assumption, param, depth) {
            if found.is_some() {
                return None;
            }
            found = Some(idx);
        }
    }
    found
}

fn is_final_view_pin(assumption: &PureExpr, param: &str, depth: usize) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = assumption else {
        return false;
    };
    (is_view_final_chain(lhs, param, depth) && is_closed_pin_value(rhs, param))
        || (is_view_final_chain(rhs, param, depth) && is_closed_pin_value(lhs, param))
}

/// `View(Final^depth(Var(param)))`, exactly.
fn is_view_final_chain(expr: &PureExpr, param: &str, depth: usize) -> bool {
    let PureExpr::View(inner) = expr else {
        return false;
    };
    let mut current = inner.as_ref();
    for _ in 0..depth {
        let PureExpr::Final(next) = current else {
            return false;
        };
        current = next.as_ref();
    }
    matches!(current, PureExpr::Var(name, _) if name == param)
}

fn is_closed_pin_value(expr: &PureExpr, param: &str) -> bool {
    !expr.any_free_var(|name, _| name == param || name == "result")
}

/// Conjunction of the `Ite` conditions (negated for else-arms) along a path.
fn guard_expr(path: &[(PureExpr, bool)]) -> PureExpr {
    let mut guards = path.iter().map(|(cond, is_then)| {
        if *is_then {
            cond.clone()
        } else {
            PureExpr::UnOp(UnOp::Not, Arc::new(cond.clone()))
        }
    });
    let first = guards.next().expect("guard path must be non-empty");
    guards.fold(first, |acc, guard| {
        PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(guard))
    })
}

/// Replace `assumptions[idx]` (an unconditional pin `P`) with
/// `Ite(guard, superseding, P)` and mirror the same replacement for any
/// identical copies in the pre-loop assumption list.
fn rewrite_pin_in_place(
    assumptions: &mut [PureExpr],
    pre_loop_assumptions: &mut [PureExpr],
    idx: usize,
    guard: &PureExpr,
    superseding: PureExpr,
) {
    let original = assumptions[idx].clone();
    let rewritten = PureExpr::Ite(
        Arc::new(guard.clone()),
        Arc::new(superseding),
        Arc::new(original.clone()),
    );
    assumptions[idx] = rewritten.clone();
    for pre in pre_loop_assumptions.iter_mut() {
        if *pre == original {
            *pre = rewritten.clone();
        }
    }
}

/// Canonical view expressions for the two sides of the stored borrow.
#[derive(Default)]
struct CanonicalStoredBorrow {
    /// `View` of the fresh constant naming the borrow's current-side value
    /// (`(*b)@`), when the match-arm substitution applied.
    current: Option<PureExpr>,
    /// `View` of the fresh constant naming the borrow's final-side value
    /// (`(^b)@`), when the match-arm substitution applied.
    final_side: Option<PureExpr>,
    /// Bridges for sibling tuple bindings (e.g. `first`): fresh constant ==
    /// payload projection expression. Asserted under the store guard so the
    /// match-arm facts (encoded with native payload selectors) connect to the
    /// goal-side placeholder selector chain.
    sibling_bridges: Vec<(PureExpr, PureExpr)>,
    /// `X == Seq::empty()` facts entailed by the nullary (None-like) arm of
    /// the two-arm match (research-doc fact F1). Asserted top-level under the
    /// non-store guard so the seq VALUE-level pin survives (the projector-only
    /// decomposition of `X == Y` never connects `X` to `seq_empty`).
    nullary_arm_empty_facts: Vec<PureExpr>,
}

/// Fix for the `(*b)@`/`(^b)@` binder conflation: when the stored value is a
/// tuple-payload projection of a `Match` call-assumption scrutinee, give the
/// bound borrow's current and final sides distinct fresh constants.
///
/// The match-arm encoder collapses temporal wrappers on binder vars to the
/// payload-projection term, so `(*b)@` and `(^b)@` encode to the SAME symbol
/// (losing the final side), and the payload selector encodes under a
/// different UF name than a driver-level `tuple_get_*` `LogicFnCall` does
/// (placeholder vs native selector), so a raw store-rhs expression would not
/// connect by congruence either. Substituting fresh named constants on both
/// sides gives the store-resolution facts and the match-arm facts a shared
/// symbol per side.
///
/// Looks for `store_rhs = tuple_get_I(<proj>(Var(scrutinee)))`, finds the
/// `Match` assumption over `Var(scrutinee)` whose constructor arm binds a
/// tuple with `Binding(b)` at index `I`, and substitutes in that arm body:
/// - `Deref(Var(b))` → `Var("__twp_current_{b}_{scrutinee}")`
/// - `Final(Var(b))` → `Var("__twp_prophecy_{b}_{scrutinee}")`
fn canonicalize_stored_borrow_sides(
    call_assumptions: &mut [PureExpr],
    store_rhs: &PureExpr,
) -> CanonicalStoredBorrow {
    let mut result = CanonicalStoredBorrow::default();
    let PureExpr::LogicFnCall { name, args } = store_rhs else {
        return result;
    };
    let Some(field_idx) = tuple_field_logic_fn_index(name) else {
        return result;
    };
    let [payload] = args.as_slice() else {
        return result;
    };
    let Some(scrutinee_name) = single_var_root(payload).map(str::to_string) else {
        return result;
    };

    for assumption in call_assumptions.iter_mut() {
        let PureExpr::Match { scrutinee, arms } = assumption else {
            continue;
        };
        let PureExpr::Var(sname, _) = scrutinee.as_ref() else {
            continue;
        };
        if *sname != scrutinee_name {
            continue;
        }
        // F1: value-level `X == Seq::empty()` facts from the nullary arm of a
        // two-arm match, to be asserted top-level under the non-store guard.
        if arms.len() == 2 {
            for arm in arms.iter() {
                if matches!(&arm.pattern, Pattern::Constructor { inner: None, .. }) {
                    for fact in empty_transitivity_additions(&arm.body) {
                        if !result.nullary_arm_empty_facts.contains(&fact) {
                            result.nullary_arm_empty_facts.push(fact);
                        }
                    }
                }
            }
        }
        for arm in arms.iter_mut() {
            let Pattern::Constructor {
                inner: Some(inner_pat),
                ..
            } = &arm.pattern
            else {
                continue;
            };
            let Pattern::Tuple(elements) = inner_pat.as_ref() else {
                continue;
            };
            let Some(Pattern::Binding(binding)) = elements.get(field_idx) else {
                continue;
            };
            let binding = binding.clone();
            let current_var =
                PureExpr::Var(format!("$twp_current_{binding}_{scrutinee_name}"), None);
            let final_var =
                PureExpr::Var(format!("$twp_prophecy_{binding}_{scrutinee_name}"), None);
            let mut current_changed = false;
            let mut final_changed = false;
            arm.body = arm.body.rewrite_bottom_up(|node| match &node {
                PureExpr::Deref(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(n, _) if *n == binding) =>
                {
                    current_changed = true;
                    current_var.clone()
                }
                PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(n, _) if *n == binding) =>
                {
                    final_changed = true;
                    final_var.clone()
                }
                _ => node,
            });
            if current_changed {
                result.current = Some(PureExpr::View(Arc::new(current_var)));
            }
            if final_changed {
                result.final_side = Some(PureExpr::View(Arc::new(final_var)));
            }

            // Sibling bindings (e.g. `first` in `Some((first, rem))`): the
            // match-arm binder collapse encodes their `*b`/`^b` facts with
            // NATIVE payload selectors, while the goal's `result`-threading
            // encodes the same payload with PLACEHOLDER selector UFs — the
            // two never meet by congruence. Substitute one fresh constant for
            // both wrappers (preserving the existing single-symbol reading of
            // the binder) and record a bridge equating it to the driver-level
            // payload projection, which encodes exactly like the goal side.
            for (sibling_idx, element) in elements.iter().enumerate() {
                if sibling_idx == field_idx {
                    continue;
                }
                let Pattern::Binding(sibling) = element else {
                    continue;
                };
                let sibling = sibling.clone();
                // Final-collapse audit Fix A (driver-side refusal): fusing
                // `*sibling` AND `^sibling` into ONE symbol — bridged to the
                // CURRENT-state payload projection below — asserts the
                // prophecy inversion `^sibling == *sibling` whenever the
                // sibling's type embeds `&mut` (the adjudicated
                // take_first_mut `idx(cur,0) == idx(fin,0)` false lemma).
                // The fused symbol reaches the encoder as a plain Var, so the
                // encoder-side sort guard cannot see it. When the arm body
                // carries a `Final(sibling)` fact whose annotation cannot be
                // proven free of `&mut` (fail-closed: missing/non-scalar
                // annotations count as embedding), SKIP the repair for this
                // binder: the raw `Final(Var(sibling))` then flows to the
                // encoder, whose sort-aware guard refuses the collapse — an
                // honest Unknown/error instead of an inverted premise.
                let final_needs_prophecy = arm.body.any_recursive(|node| {
                    let PureExpr::Final(inner) = node else {
                        return false;
                    };
                    matches!(
                        inner.as_ref(),
                        PureExpr::Var(n, ann)
                            if *n == sibling && sibling_annotation_may_embed_mut_ref(ann.as_ref())
                    )
                });
                if final_needs_prophecy {
                    trace!(
                        sibling = sibling.as_str(),
                        scrutinee = scrutinee_name.as_str(),
                        "store-prophecy repair: refusing sibling Deref+Final fusion \
                         (annotation may embed &mut; encoder guard will handle raw Final)"
                    );
                    continue;
                }
                let sibling_var =
                    PureExpr::Var(format!("$twp_payload_{sibling}_{scrutinee_name}"), None);
                let mut sibling_changed = false;
                arm.body = arm.body.rewrite_bottom_up(|node| match &node {
                    PureExpr::Deref(inner) | PureExpr::Final(inner)
                        if matches!(inner.as_ref(), PureExpr::Var(n, _) if *n == sibling) =>
                    {
                        sibling_changed = true;
                        sibling_var.clone()
                    }
                    _ => node,
                });
                if sibling_changed {
                    let projection = PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(sibling_idx),
                        args: vec![payload.clone()],
                    };
                    let bridge = (sibling_var, projection);
                    if !result.sibling_bridges.contains(&bridge) {
                        result.sibling_bridges.push(bridge);
                    }
                }
            }
        }
    }
    result
}

/// Fail-closed, registry-free check for the sibling-fusion refusal (Fix A):
/// may the sibling binder's annotated sort embed a mutable reference?
///
/// Only annotations that provably denote pure value sorts allow the fusion;
/// everything else — missing annotations (the common case for spec-axiom
/// binders), `MutRef`, datatypes, tuples, references, type parameters —
/// counts as embedding. Mirrors the encoder-side
/// `final_collapse_guard::expr_sort_may_embed_mut_ref_syntactic` contract at
/// the driver layer (no ADT registry available here).
fn sibling_annotation_may_embed_mut_ref(ann: Option<&trust_wp_core::formula::ExprSort>) -> bool {
    use trust_wp_core::formula::ExprSort;
    match ann {
        None => true,
        Some(
            ExprSort::Int
            | ExprSort::Bool
            | ExprSort::Seq
            | ExprSort::Unit
            | ExprSort::FMap
            | ExprSort::Float(_),
        ) => false,
        Some(_) => true,
    }
}

/// Facts `X == Seq::empty()` entailed by transitivity from a conjunction
/// containing `X == Y` and `Y == Seq::empty()` (either orientation),
/// research-doc fact F1.
///
/// Only the `== Seq::empty()` target shape is derived because the encoder
/// asserts seq VALUE-level equality only for that shape; other Seq equalities
/// decompose into projector equalities, leaving `X` and `seq_empty`
/// disconnected in the E-graph.
fn empty_transitivity_additions(body: &PureExpr) -> Vec<PureExpr> {
    fn is_seq_empty(expr: &PureExpr) -> bool {
        matches!(
            expr,
            PureExpr::LogicFnCall { name, args }
                if args.is_empty() && (name == "Seq::empty" || name == "Seq::EMPTY")
        )
    }
    fn flatten<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
        if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
            flatten(lhs, out);
            flatten(rhs, out);
        } else {
            out.push(expr);
        }
    }

    let mut conjuncts = Vec::new();
    flatten(body, &mut conjuncts);

    // Terms directly equated to Seq::empty().
    let mut empty_terms: Vec<&PureExpr> = Vec::new();
    for conjunct in &conjuncts {
        if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = conjunct {
            if is_seq_empty(rhs) && !is_seq_empty(lhs) {
                empty_terms.push(lhs.as_ref());
            } else if is_seq_empty(lhs) && !is_seq_empty(rhs) {
                empty_terms.push(rhs.as_ref());
            }
        }
    }
    if empty_terms.is_empty() {
        return Vec::new();
    }

    let mut additions: Vec<PureExpr> = Vec::new();
    for conjunct in &conjuncts {
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = conjunct else {
            continue;
        };
        for (side, other) in [(lhs, rhs), (rhs, lhs)] {
            if empty_terms.iter().any(|t| *t == side.as_ref())
                && !is_seq_empty(other)
                && !empty_terms.iter().any(|t| *t == other.as_ref())
            {
                let derived = PureExpr::BinOp(
                    other.clone(),
                    BinOp::Eq,
                    Arc::new(PureExpr::LogicFnCall {
                        name: "Seq::empty".to_string(),
                        args: vec![],
                    }),
                );
                if !additions.contains(&derived) {
                    additions.push(derived);
                }
            }
        }
    }
    additions
}

/// Root variable of a single-argument projection chain
/// (`f(g(...(Var(x))))` → `x`).
fn single_var_root(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name),
        PureExpr::LogicFnCall { args, .. } if args.len() == 1 => single_var_root(&args[0]),
        _ => None,
    }
}

/// Replace the store fact's assumption with `true` (the superseding facts now
/// carry its semantics; the raw form incorrectly pinned the entry carrier).
fn neutralize_store_assume(expr: &PureExpr, param: &str) -> PureExpr {
    expr.rewrite_bottom_up(|node| {
        if let PureExpr::LetAssume { assumption, body } = &node {
            if param_store_rhs(assumption, param).is_some() {
                return PureExpr::LetAssume {
                    assumption: Arc::new(PureExpr::Bool(true)),
                    body: body.clone(),
                };
            }
        }
        node
    })
}

/// Neutralize the entry-carrier deref-store facts of plain `&mut T` params.
///
/// MIR extraction records every `*p = <rhs>` through a `&mut` parameter as a
/// projected write fact, and `wrap_projected_facts` turns it into a
/// `LetAssume { *p == <rhs>, .. }` hypothesis on the enclosing path. In the
/// RustHorn encoding `*p` is the ENTRY carrier `p_current`, so that hypothesis
/// does not say "the store happened" — it says "the value the caller passed in
/// already equals `<rhs>`", which is false in general and OUTRIGHT
/// CONTRADICTORY whenever `<rhs>` reads `*p` (measured on
/// `if *v < 0 { *v = -*v; }` → `(or (not (< v 0)) (= v (- v)))`, and on
/// `if *v < 0 { *v = *v - 1; }` → `(or (not (< v 0)) (= v (+ v (- 1))))`).
///
/// A contradictory branch hypothesis makes that branch vacuous, so every
/// postcondition — true or false — closes on it. The same defect for nested
/// `&mut &mut` params is already described and neutralized above; there it is
/// masked because the equality drops out as an ill-sorted coercion constant,
/// while for a plain `&mut T` it is well sorted and reaches the solver.
///
/// The store's real content is carried elsewhere and correctly: the per-borrow
/// carrier expiry facts resolve the prophecy as `^p == Ite(guard, <rhs>, …)`
/// (the `ite_int_aux` chain in the emitted query). This pass therefore only
/// DELETES a false hypothesis; it adds nothing. Dropping a hypothesis is a pure
/// weakening — it can only turn a provable obligation into an unprovable one,
/// never the reverse — so it cannot create a verdict.
///
/// Scope: parameters whose type is `&mut T` with `T` NOT itself a `&mut`.
/// Nested `&mut &mut` parameters keep the existing, tightly gated treatment.
pub(super) fn neutralize_plain_mut_ref_entry_store_facts(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    parsed: &mut ParsedContract,
) {
    let params = plain_mut_ref_param_names(tcx, def_id, &parsed.arg_names);
    if params.is_empty() {
        return;
    }
    for param in params {
        if let Some(expr) = parsed.result_expr.take() {
            parsed.result_expr = Some(neutralize_deref_store_assume(&expr, &param));
        }
        if let Some(spanned) = parsed.result_expr_spanned.as_mut() {
            spanned.expr = neutralize_deref_store_assume(&spanned.expr, &param);
        }
        trace!(
            param = %param,
            "entry-carrier deref-store hypothesis neutralized"
        );
    }
}

/// Names of parameters with plain (non-nested) `&mut _` type.
fn plain_mut_ref_param_names(tcx: TyCtxt<'_>, def_id: DefId, arg_names: &[String]) -> Vec<String> {
    // Closures don't have fn_sig(); their parameters are captures.
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return Vec::new();
    }
    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip();
    let sig = tcx.liberate_late_bound_regions(def_id, sig);
    sig.inputs()
        .iter()
        .zip(arg_names)
        .filter_map(|(ty, name)| match ty.kind() {
            TyKind::Ref(_, inner, Mutability::Mut)
                if !matches!(inner.kind(), TyKind::Ref(_, _, Mutability::Mut)) =>
            {
                Some(name.clone())
            }
            _ => None,
        })
        .collect()
}

/// Replace every `LetAssume { *param == <rhs>, .. }` with `LetAssume { true, .. }`.
///
/// Deliberately narrower than [`neutralize_store_assume`]: only the `Deref`
/// spelling produced by `wrap_projected_facts` for a deref store is matched, so
/// no other hypothesis about `param` is disturbed.
fn neutralize_deref_store_assume(expr: &PureExpr, param: &str) -> PureExpr {
    expr.rewrite_bottom_up(|node| {
        if let PureExpr::LetAssume { assumption, body } = &node {
            if is_deref_store_of_param(assumption, param) {
                return PureExpr::LetAssume {
                    assumption: Arc::new(PureExpr::Bool(true)),
                    body: body.clone(),
                };
            }
        }
        node
    })
}

/// True for the exact deref-store hypothesis shape `*param == <rhs>`.
fn is_deref_store_of_param(assumption: &PureExpr, param: &str) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, _) = assumption else {
        return false;
    };
    let PureExpr::Deref(inner) = lhs.as_ref() else {
        return false;
    };
    matches!(inner.as_ref(), PureExpr::Var(name, _) if name == param)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn view_final(param: &str, depth: usize) -> PureExpr {
        let mut expr = var(param);
        for _ in 0..depth {
            expr = PureExpr::Final(Arc::new(expr));
        }
        PureExpr::View(Arc::new(expr))
    }

    fn empty_seq() -> PureExpr {
        PureExpr::LogicFnCall {
            name: "Seq::empty".to_string(),
            args: vec![],
        }
    }

    fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
    }

    #[test]
    fn detects_view_final_chain_depths() {
        assert!(is_view_final_chain(&view_final("p", 1), "p", 1));
        assert!(is_view_final_chain(&view_final("p", 2), "p", 2));
        assert!(!is_view_final_chain(&view_final("p", 1), "p", 2));
        assert!(!is_view_final_chain(&view_final("q", 1), "p", 1));
        // Final(Old(Deref(p))) must NOT match (it is a different borrow).
        let old_deref = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Old(
            Arc::new(PureExpr::Deref(Arc::new(var("p")))),
        )))));
        assert!(!is_view_final_chain(&old_deref, "p", 1));
    }

    #[test]
    fn collects_branch_scoped_store_with_guard_path() {
        let cond = eq(var("d"), PureExpr::Int(0));
        let store = eq(var("p"), var("rem"));
        let expr = PureExpr::Ite(
            Arc::new(cond.clone()),
            Arc::new(var("none_result")),
            Arc::new(PureExpr::LetAssume {
                assumption: Arc::new(store),
                body: Arc::new(var("some_result")),
            }),
        );
        let mut out = Vec::new();
        collect_param_store_assumes(&expr, "p", &mut Vec::new(), &mut out);
        assert_eq!(out.len(), 1);
        let (path, rhs) = &out[0];
        assert_eq!(rhs, &var("rem"));
        assert_eq!(path.len(), 1);
        assert_eq!(path[0], (cond, false));
    }

    #[test]
    fn pin_lookup_requires_closed_rhs_and_uniqueness() {
        let pin = eq(view_final("p", 1), empty_seq());
        let self_ref = eq(view_final("p", 1), PureExpr::Deref(Arc::new(var("p"))));
        assert_eq!(find_unconditional_pin(&[pin.clone()], "p", 1), Some(0));
        assert_eq!(find_unconditional_pin(&[self_ref], "p", 1), None);
        // Two pins of the same depth: ambiguous, bail.
        assert_eq!(find_unconditional_pin(&[pin.clone(), pin], "p", 1), None);
    }

    #[test]
    fn neutralizes_only_the_param_store_assume() {
        let store = eq(var("p"), var("rem"));
        let other = eq(var("q"), var("x"));
        let expr = PureExpr::LetAssume {
            assumption: Arc::new(store),
            body: Arc::new(PureExpr::LetAssume {
                assumption: Arc::new(other.clone()),
                body: Arc::new(var("r")),
            }),
        };
        let result = neutralize_store_assume(&expr, "p");
        let PureExpr::LetAssume { assumption, body } = &result else {
            panic!("expected LetAssume");
        };
        assert_eq!(assumption.as_ref(), &PureExpr::Bool(true));
        let PureExpr::LetAssume {
            assumption: inner_assumption,
            ..
        } = body.as_ref()
        else {
            panic!("expected inner LetAssume");
        };
        assert_eq!(inner_assumption.as_ref(), &other);
    }

    #[test]
    fn canonicalize_gives_match_binding_sides_distinct_symbols() {
        use trust_wp_core::formula::MatchArm;

        // store_rhs = tuple_get_1(tuple_get_0(call_2))
        let store_rhs = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_1".to_string(),
            args: vec![PureExpr::LogicFnCall {
                name: "__trust_wp_tuple_get_0".to_string(),
                args: vec![var("call_2")],
            }],
        };
        // Match call_2 {
        //   Some((first, rem)) => (*rem)@ == tail_cur && (^rem)@ == tail_fin,
        //   None => true,
        // }
        let some_body = PureExpr::BinOp(
            Arc::new(eq(
                PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(var("rem"))))),
                var("tail_of_current"),
            )),
            BinOp::And,
            Arc::new(eq(
                PureExpr::View(Arc::new(PureExpr::Final(Arc::new(var("rem"))))),
                var("tail_of_final"),
            )),
        );
        let mut assumptions = vec![PureExpr::Match {
            scrutinee: Arc::new(var("call_2")),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Tuple(vec![
                            Pattern::Binding("first".to_string()),
                            Pattern::Binding("rem".to_string()),
                        ]))),
                    },
                    body: some_body,
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Bool(true),
                },
            ],
        }];

        let canonical = canonicalize_stored_borrow_sides(&mut assumptions, &store_rhs);
        let current = canonical.current.expect("current side should canonicalize");
        let final_side = canonical
            .final_side
            .expect("final side should canonicalize");
        let PureExpr::View(cur_inner) = &current else {
            panic!("expected View");
        };
        let PureExpr::View(fin_inner) = &final_side else {
            panic!("expected View");
        };
        assert_eq!(
            cur_inner.as_ref(),
            &var("$twp_current_rem_call_2"),
            "current-side canonical var"
        );
        assert_eq!(
            fin_inner.as_ref(),
            &var("$twp_prophecy_rem_call_2"),
            "final-side canonical var"
        );

        // The arm body now references the fresh vars instead of *rem/^rem.
        let PureExpr::Match { arms, .. } = &assumptions[0] else {
            panic!("expected Match");
        };
        let expected = PureExpr::BinOp(
            Arc::new(eq(
                PureExpr::View(Arc::new(var("$twp_current_rem_call_2"))),
                var("tail_of_current"),
            )),
            BinOp::And,
            Arc::new(eq(
                PureExpr::View(Arc::new(var("$twp_prophecy_rem_call_2"))),
                var("tail_of_final"),
            )),
        );
        assert_eq!(arms[0].body, expected);
    }

    #[test]
    fn canonicalize_bridges_sibling_binding_to_payload_projection() {
        use trust_wp_core::formula::MatchArm;

        let store_rhs = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_1".to_string(),
            args: vec![PureExpr::LogicFnCall {
                name: "__trust_wp_tuple_get_0".to_string(),
                args: vec![var("call_2")],
            }],
        };
        // Arm body only mentions the SIBLING binding `first` — the stored
        // binding `rem` (index 1) does not occur, so no stored-borrow symbols
        // are returned, but the sibling is canonicalized to one payload
        // constant with a projection bridge (conflation-preserving).
        let some_body = eq(
            PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(var("first"))))),
            var("head"),
        );
        let mut assumptions = vec![PureExpr::Match {
            scrutinee: Arc::new(var("call_2")),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("first".to_string()),
                        Pattern::Binding("rem".to_string()),
                    ]))),
                },
                body: some_body,
            }],
        }];

        let canonical = canonicalize_stored_borrow_sides(&mut assumptions, &store_rhs);
        assert!(canonical.current.is_none());
        assert!(canonical.final_side.is_none());
        assert_eq!(canonical.sibling_bridges.len(), 1);
        let (fresh, projection) = &canonical.sibling_bridges[0];
        assert_eq!(fresh, &var("$twp_payload_first_call_2"));
        let expected_projection = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::LogicFnCall {
                name: "__trust_wp_tuple_get_0".to_string(),
                args: vec![var("call_2")],
            }],
        };
        assert_eq!(projection, &expected_projection);
        // The arm's `*first` occurrence now references the fresh constant.
        let PureExpr::Match { arms, .. } = &assumptions[0] else {
            panic!("expected Match");
        };
        let expected_body = eq(
            PureExpr::View(Arc::new(var("$twp_payload_first_call_2"))),
            var("head"),
        );
        assert_eq!(arms[0].body, expected_body);
    }

    #[test]
    fn canonicalize_refuses_sibling_fusion_when_final_needs_prophecy() {
        use trust_wp_core::formula::MatchArm;

        // Final-collapse audit Fix A (driver-side refusal): when the arm body
        // carries BOTH `*first` and `^first` facts and the binder's
        // annotation cannot be proven free of `&mut` (here: unannotated —
        // the SPLIT_FIRST_MUT spec-axiom shape), fusing both wrappers into
        // ONE `__twp_payload_*` symbol would assert the take_first_mut
        // inversion. The sibling substitution must be SKIPPED entirely: raw
        // wrappers stay in the body (the encoder's sort-aware guard then
        // refuses the Final collapse — honest Unknown/error, never an
        // inverted premise), and no projection bridge is minted.
        let store_rhs = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_1".to_string(),
            args: vec![PureExpr::LogicFnCall {
                name: "__trust_wp_tuple_get_0".to_string(),
                args: vec![var("call_2")],
            }],
        };
        let some_body = PureExpr::BinOp(
            Arc::new(eq(PureExpr::Deref(Arc::new(var("first"))), var("head_cur"))),
            BinOp::And,
            Arc::new(eq(PureExpr::Final(Arc::new(var("first"))), var("head_fin"))),
        );
        let original_body = some_body.clone();
        let mut assumptions = vec![PureExpr::Match {
            scrutinee: Arc::new(var("call_2")),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("first".to_string()),
                        Pattern::Binding("rem".to_string()),
                    ]))),
                },
                body: some_body,
            }],
        }];

        let canonical = canonicalize_stored_borrow_sides(&mut assumptions, &store_rhs);
        assert!(
            canonical.sibling_bridges.is_empty(),
            "no fused-symbol bridge may be minted for a Final-carrying sibling"
        );
        let PureExpr::Match { arms, .. } = &assumptions[0] else {
            panic!("expected Match");
        };
        assert_eq!(
            arms[0].body, original_body,
            "sibling wrappers must be left RAW (Deref+Final untouched) so the \
             encoder-side guard sees the Final"
        );
    }

    #[test]
    fn sibling_annotation_embed_check_is_fail_closed() {
        use trust_wp_core::formula::ExprSort;

        assert!(sibling_annotation_may_embed_mut_ref(None));
        assert!(sibling_annotation_may_embed_mut_ref(Some(
            &ExprSort::MutRef(Box::new(ExprSort::Int))
        )));
        assert!(sibling_annotation_may_embed_mut_ref(Some(
            &ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("Opt"))
        )));
        assert!(sibling_annotation_may_embed_mut_ref(Some(
            &ExprSort::Tuple(2)
        )));
        // Provably pure value sorts allow the (sound) fusion.
        assert!(!sibling_annotation_may_embed_mut_ref(Some(&ExprSort::Int)));
        assert!(!sibling_annotation_may_embed_mut_ref(Some(&ExprSort::Seq)));
        assert!(!sibling_annotation_may_embed_mut_ref(Some(&ExprSort::Bool)));
    }
}
