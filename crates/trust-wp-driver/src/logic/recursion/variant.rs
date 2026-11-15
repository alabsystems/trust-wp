// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Variant validation and termination-decrease proof for mutual recursion.
//!
//! Checks that each SCC member has a well-formed integer variant expression,
//! then proves that each intra-SCC call edge strictly decreases the variant.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_ay::{verify_function_with_modes, VerificationRequest, VerificationResult};
use trust_wp_core::{
    formula::{resolve_sort_name, BinOp, ExprSort, PureExpr, UnOp},
    TrackLevel,
};

use super::{
    super::discovery::{machine_int_range, MachineIntWidth},
    call_edges::LogicCallEdge,
    graph::{edge_name, self_edge_name},
    LogicRecursionNode,
};

/// Errors from variant validation and termination-decrease proof.
#[derive(Debug, Clone, thiserror::Error)]
pub(super) enum VariantError {
    #[error("variant for {full_path} must be integer-valued")]
    NotIntegerValued { full_path: String },

    #[error("variant for {full_path} uses unsupported non-integer syntax")]
    UnsupportedIntSyntax { full_path: String },

    #[error("path condition for {full_path} uses unsupported non-bool syntax")]
    UnsupportedBoolSyntax { full_path: String },

    #[error("path condition for {full_path} uses unsupported control flow")]
    UnsupportedControlFlow { full_path: String },

    #[error("callee arity mismatch: expected {expected}, got {actual}")]
    ArityMismatch { expected: usize, actual: usize },

    #[error("variant obligation encoding failed: {reason}")]
    EncodingFailed { reason: String },

    #[error("variant obligation was assumed instead of proven")]
    ObligationAssumed,

    #[error("variant obligation could not be proved")]
    ObligationFailed,

    #[error("variant obligation returned unknown: {reason}")]
    ObligationUnknown { reason: String },

    #[error("variant obligation returned an unsupported solver result")]
    UnsupportedResult,
}

#[allow(clippy::similar_names)] // caller/callee prefixes are domain-distinct
pub(super) fn validate_supported_mutual_recursion_scc(
    component: &[usize],
    nodes: &[LogicRecursionNode],
    graph: &HashMap<usize, HashSet<usize>>,
    parsed_edges: &[LogicCallEdge],
) -> Result<(), (String, String)> {
    let component_set: HashSet<usize> = component.iter().copied().collect();
    let mut variants_by_idx: HashMap<usize, &PureExpr> = HashMap::new();

    for &idx in component {
        let edge_name = self_edge_name(nodes, idx);
        if !nodes[idx].variant_parse_errors.is_empty() {
            return Err((edge_name, nodes[idx].variant_parse_errors.join("; ")));
        }
        if nodes[idx].raw_variants.len() != 1 || nodes[idx].parsed_variants.len() != 1 {
            return Err((
                edge_name,
                format!(
                    "{} must have exactly one parsed #[variant(...)] for mutual recursion",
                    nodes[idx].full_path
                ),
            ));
        }

        let variant = &nodes[idx].parsed_variants[0];
        ensure_supported_int_variant(
            variant,
            &nodes[idx].params,
            &nodes[idx].param_sort_hints,
            &nodes[idx].full_path,
        )
        .map_err(|e| (self_edge_name(nodes, idx), e.to_string()))?;
        variants_by_idx.insert(idx, variant);
    }

    for &caller_idx in component {
        let Some(callees) = graph.get(&caller_idx) else {
            continue;
        };
        let mut sorted_callees: Vec<usize> = callees
            .iter()
            .copied()
            .filter(|callee_idx| component_set.contains(callee_idx))
            .collect();
        sorted_callees.sort_unstable();

        for callee_idx in sorted_callees {
            let pair_edges: Vec<&LogicCallEdge> = parsed_edges
                .iter()
                .filter(|edge| edge.caller_idx == caller_idx && edge.callee_idx == callee_idx)
                .collect();
            let pair_edge_name = edge_name(nodes, caller_idx, callee_idx);

            if pair_edges.is_empty() {
                return Err((
                    pair_edge_name,
                    "call edge is only recoverable from text/requires/ensures scanning".to_string(),
                ));
            }

            let structured_edges: Vec<&LogicCallEdge> = pair_edges
                .iter()
                .copied()
                .filter(|edge| !edge.recovered_from_text_only)
                .collect();
            if structured_edges.is_empty() {
                return Err((
                    pair_edge_name,
                    "call edge is only recoverable from text scanning".to_string(),
                ));
            }

            for edge in structured_edges {
                if let Some(reason) = edge.unsupported_reason.as_ref() {
                    return Err((pair_edge_name.clone(), reason.clone()));
                }
                if let Some(shadowed) = edge
                    .enclosing_binders
                    .iter()
                    .find(|binder| nodes[caller_idx].params.contains(binder))
                {
                    return Err((
                        pair_edge_name.clone(),
                        format!(
                            "a binder shadows parameter `{shadowed}` around the call, so its \
                             arguments cannot be related to the caller's variant"
                        ),
                    ));
                }

                let caller_variant = variants_by_idx
                    .get(&caller_idx)
                    .expect("caller variant should be recorded");
                let callee_variant = variants_by_idx
                    .get(&callee_idx)
                    .expect("callee variant should be recorded");
                prove_mutual_variant_decrease(
                    caller_variant,
                    &nodes[caller_idx].requires,
                    &nodes[caller_idx].params,
                    &nodes[caller_idx].param_sort_hints,
                    callee_variant,
                    &nodes[callee_idx].params,
                    &nodes[callee_idx].param_int_widths,
                    edge,
                )
                .map_err(|e| (pair_edge_name.clone(), e.to_string()))?;
            }
        }
    }

    Ok(())
}

/// Outcome of attempting a solver-backed decrease proof for a single-function
/// self-recursive logic fn that carries `#[variant(...)]`.
#[derive(Debug)]
pub(super) enum SelfVariantDecrease {
    /// No decrease proof could be produced: the variant and/or a self-call edge
    /// is outside the modelled fragment (non-Int variant, method/`Self::`
    /// dispatch, quantifier/closure-scoped recursion, text-only edges, a
    /// parse-failed body, arity mismatch) or the solver did not return a
    /// checked `Verified`. The reason is carried for the diagnostic. The caller
    /// MUST reject: a `#[variant]` recursion without a decrease proof is not
    /// credited (its defining equation may be inconsistent, `f(x) = f(x) + 1`).
    Unsupported(String),
    /// Every structured self-edge was proven to strictly decrease the variant.
    Proven,
    /// At least one self-edge could not be proven to decrease the variant; the
    /// solver returned a definitive `Failed`.
    Failed(String),
}

/// Attempt to discharge the per-edge variant-decrease obligation for the single
/// self-recursive node `idx` using the SMT backend.
///
/// Soundness contract (fail-closed):
/// - `Proven` only when the variant is a supported integer expression, there
///   is at least one structured self-edge, EVERY structured self-edge is inside
///   the modelled fragment (no `unsupported_reason`, arity matches), and each
///   one discharges under strict trust (or the requires are proven
///   unsatisfiable).
/// - `Failed` on a definitive solver `Failed`.
/// - `Unsupported(reason)` otherwise; the caller rejects it.
///
/// `parsed_edges` must be the variant-proof edge view
/// (`collect_variant_proof_call_edges`), in which match-arm binders are renamed
/// apart and bound to what the pattern literally extracts.
#[allow(clippy::similar_names)]
pub(super) fn try_prove_self_variant_decrease(
    idx: usize,
    nodes: &[LogicRecursionNode],
    graph: &HashMap<usize, HashSet<usize>>,
    parsed_edges: &[LogicCallEdge],
) -> SelfVariantDecrease {
    let node = &nodes[idx];
    // Parse-failed bodies have no trustworthy structured edges.
    if node.body_parse_failed {
        return SelfVariantDecrease::Unsupported("the body could not be parsed".to_string());
    }
    if !node.variant_parse_errors.is_empty() {
        return SelfVariantDecrease::Unsupported(node.variant_parse_errors.join("; "));
    }
    if node.raw_variants.len() != 1 || node.parsed_variants.len() != 1 {
        return SelfVariantDecrease::Unsupported(
            "exactly one parsed #[variant(...)] is required".to_string(),
        );
    }

    let variant = &node.parsed_variants[0];
    if let Err(error) = ensure_supported_int_variant(
        variant,
        &node.params,
        &node.param_sort_hints,
        &node.full_path,
    ) {
        return SelfVariantDecrease::Unsupported(error.to_string());
    }

    // There must be a self-edge in the graph at all.
    if !graph
        .get(&idx)
        .is_some_and(|callees| callees.contains(&idx))
    {
        return SelfVariantDecrease::Unsupported("no self-call edge was found".to_string());
    }

    let self_edges: Vec<&LogicCallEdge> = parsed_edges
        .iter()
        .filter(|edge| edge.caller_idx == idx && edge.callee_idx == idx)
        .collect();

    // Restrict to structured (AST-derived) edges; text-only edges carry no
    // actual_args/path_conditions and are conservative duplicates.
    let structured: Vec<&LogicCallEdge> = self_edges
        .iter()
        .copied()
        .filter(|edge| !edge.recovered_from_text_only)
        .collect();
    if structured.is_empty() {
        // Only text-recoverable self-edges => the structured view of the body is
        // incomplete (or the call is a method/dispatch form).
        return SelfVariantDecrease::Unsupported(
            "the self-call is only recoverable from text scanning".to_string(),
        );
    }

    // Every structured self-edge must be inside the supported fragment.
    for edge in &structured {
        if let Some(reason) = &edge.unsupported_reason {
            return SelfVariantDecrease::Unsupported(reason.clone());
        }
        if edge.actual_args.len() != node.params.len() {
            return SelfVariantDecrease::Unsupported(format!(
                "self-call arity mismatch: expected {}, got {}",
                node.params.len(),
                edge.actual_args.len()
            ));
        }
    }

    // Unsatisfiable own `#[requires]` (bug/1204 `evil`, `#[requires(false)]`).
    // Creusot's decrease goal is `requires -> well_founded(variant, variant')`
    // (1204.coma `vc_evil: false -> ...`), valid when the requires is. Proving
    // the requires unsatisfiable directly -- `|- !(r1 && .. && rn)`, with NO
    // hypotheses, so no vacuity shortcut is involved -- discharges every edge.
    // It is also exactly why accepting such a function is harmless: its
    // defining axiom is guarded by the same requires
    // (`forall x. false -> evil x = evil(-x) + 1`), so it states nothing.
    if requires_proven_unsatisfiable(&node.requires, &node.params, &node.param_sort_hints) {
        return SelfVariantDecrease::Proven;
    }

    // Discharge decrease for each supported structured self-edge.
    for edge in &structured {
        match prove_self_variant_decrease(
            &node.name,
            variant,
            &node.requires,
            &node.params,
            &node.param_sort_hints,
            &node.param_int_widths,
            edge,
        ) {
            Ok(()) => {}
            Err(VariantError::ObligationFailed) => {
                return SelfVariantDecrease::Failed(format!(
                    "variant `{}` does not strictly decrease at self-call {}",
                    node.raw_variants[0],
                    self_edge_name(nodes, idx)
                ));
            }
            // Unknown / Assumed / encoding / unsupported-result: no checked
            // proof, so nothing is credited.
            Err(error) => return SelfVariantDecrease::Unsupported(error.to_string()),
        }
    }

    SelfVariantDecrease::Proven
}

/// `true` only when the solver PROVES `!(r1 && ... && rn)` with no hypotheses
/// under strict trust, i.e. the conjunction of `requires` has no model.
/// Empty `requires`, or any non-`Verified` outcome, yields `false`.
///
/// The query carries no sort information beyond the variables' own
/// annotations, so it is only meaningful when every free variable of the
/// requires is a parameter of integer or boolean sort. Anything else -- a
/// float (`!(x <= x)` holds at NaN under IEEE, yet reads unsatisfiable over an
/// ordered sort), an ADT, a sequence, an unknown sort, or a name that is not a
/// parameter -- REFUSES the shortcut (`false`), leaving the per-edge proof.
fn requires_proven_unsatisfiable(
    requires: &[PureExpr],
    params: &[String],
    param_sort_hints: &[Option<ExprSort>],
) -> bool {
    let param_sorts = param_sort_map(params, param_sort_hints);
    let all_vars_int_or_bool = requires.iter().all(|req| {
        req.free_vars().iter().all(|name| {
            param_sorts.get(name.as_str()).is_some_and(|sort| {
                matches!(sort, Some(ExprSort::Int | ExprSort::Bool))
                    || matches!(sort, Some(ExprSort::Datatype(id))
                        if is_logic_int_datatype_name(&resolve_sort_name(*id)))
            })
        })
    });
    // Binders carry their own sorts, which the check above does not see.
    let has_binder = std::cell::Cell::new(false);
    for req in requires {
        let _ = req.rewrite_bottom_up(|node| {
            if matches!(
                node,
                PureExpr::Forall { .. }
                    | PureExpr::Exists { .. }
                    | PureExpr::Match { .. }
                    | PureExpr::Let { .. }
                    | PureExpr::Closure { .. }
            ) {
                has_binder.set(true);
            }
            node
        });
    }
    if !all_vars_int_or_bool || has_binder.get() {
        return false;
    }
    let Some(conjunction) = requires
        .iter()
        .cloned()
        .reduce(|acc, req| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(req)))
    else {
        return false;
    };
    let goal = vec![PureExpr::UnOp(UnOp::Not, Arc::new(conjunction))];
    let no_hypotheses: Vec<PureExpr> = Vec::new();
    matches!(
        verify_function_with_modes(
            VerificationRequest::new(&no_hypotheses, &goal).track(Some(TrackLevel::Auto)),
        )
        .map(|result| result.apply_strict_trust(true)),
        Ok(VerificationResult::Verified(_))
    )
}

#[cfg(test)]
pub(super) fn requires_proven_unsatisfiable_for_test(
    requires: &[PureExpr],
    params: &[String],
    param_sort_hints: &[Option<ExprSort>],
) -> bool {
    requires_proven_unsatisfiable(requires, params, param_sort_hints)
}

/// Prove that `variant[args] < variant` (well-founded on Int) at one self-call.
///
/// Mirrors Creusot's `well_founded_relation_Int(before, after) = before >= 0 &&
/// before > after` (creusot-std/src/logic/well_founded.rs:40) discharged under
/// the function's own #[requires] plus the call-site path conditions ONLY.
///
/// BOTH conjuncts are goals. There is no implicit Int-variant precondition:
/// the `i >= 0 ->` in simple_trigger.coma `vc_id` is `id`'s own
/// `#[requires(i >= 0)]`, and bug/1204.coma `vc_evil` carries no such guard.
/// Assuming `before >= 0` would discharge the first conjunct for free and
/// accept `#[variant(x)] fn osc(x: Int) { if x != 0 { osc(-x) + 1 } else { 0 } }`
/// (query `x != 0, x >= 0 |- x >= 0 && -x < x`), whose defining axiom is
/// inconsistent (`osc(1) = osc(-1) + 1 = osc(1) + 2`); Creusot rejects it at
/// `x = -1`.
///
/// Machine-integer parameters (`u64`, `i32`, ...) are carried as `Int`. Their
/// Rust type ranges reach this query ONLY through `requires`: for a `#[variant]`
/// logic fn, `to_logic_fn_def` adds `min <= p <= max` to the parsed requires,
/// which also guards the defining axiom and every unfolding. That guard is what
/// makes the range a sound hypothesis here — a range-vacuous edge (`x: u8`,
/// path `x@ > 300`) describes a call that can only happen outside the domain
/// where the equation holds. `min <= arg <= max` for every machine-integer
/// argument is an extra GOAL: without it, `#[variant(x)] fn f(x: u64) { if x !=
/// 0 { f(0 - x) } }` would prove `0 <= x && -x < x` from `0 <= x` although the
/// recursion leaves the guarded domain.
#[allow(clippy::similar_names)]
fn prove_self_variant_decrease(
    own_name: &str,
    variant: &PureExpr,
    requires: &[PureExpr],
    params: &[String],
    param_sort_hints: &[Option<ExprSort>],
    param_int_widths: &[Option<MachineIntWidth>],
    edge: &LogicCallEdge,
) -> Result<(), VariantError> {
    if params.len() != edge.actual_args.len() {
        return Err(VariantError::ArityMismatch {
            expected: params.len(),
            actual: edge.actual_args.len(),
        });
    }

    let mut substitutions = HashMap::new();
    for (param, arg) in params.iter().zip(edge.actual_args.iter()) {
        substitutions.insert(param.clone(), arg.clone());
    }

    let before = variant.clone();
    let after = variant.substitute(&substitutions);
    let nonneg_before = PureExpr::BinOp(
        Arc::new(PureExpr::Int(0)),
        BinOp::Le,
        Arc::new(before.clone()),
    );

    // Goal: before >= 0 && after < before  (well_founded_relation_Int), plus
    // every machine-integer argument lies in its callee parameter's range.
    let mut ensures = vec![
        nonneg_before,
        PureExpr::BinOp(Arc::new(after), BinOp::Lt, Arc::new(before)),
    ];
    ensures.extend(argument_range_goals(param_int_widths, &edge.actual_args));

    // Hypotheses: own #[requires] (including the machine-integer parameter
    // ranges that also guard the definition) + accumulated path conditions.
    // `before >= 0` is a GOAL, never a hypothesis (see the doc comment).
    let mut hypotheses = requires.to_vec();
    hypotheses.extend(
        edge.path_conditions
            .iter()
            .filter(|condition| !reads_own_value(condition, own_name))
            .cloned(),
    );
    split_integer_disequality_hypotheses(
        &mut hypotheses,
        &param_sort_map(params, param_sort_hints),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&hypotheses, &ensures).track(Some(TrackLevel::Auto)),
    )
    .map_err(|error| VariantError::EncodingFailed {
        reason: error.to_string(),
    })?
    .apply_strict_trust(true);

    match result {
        VerificationResult::Verified(_) => Ok(()),
        VerificationResult::Assumed(_) => Err(VariantError::ObligationAssumed),
        VerificationResult::Failed(_) => Err(VariantError::ObligationFailed),
        VerificationResult::Unknown(reason) => Err(VariantError::ObligationUnknown {
            reason: reason.to_string(),
        }),
        _ => Err(VariantError::UnsupportedResult),
    }
}

/// Whether `condition` applies the function being defined (`own_name`, by its
/// last path segment).
///
/// Such a path condition guards a later USE of the recursive call's value:
/// `let rec = set_max(s); if x >= rec { x } else { rec }` reaches the call
/// again under `!(x >= set_max(s))` (bug/vcgen). Creusot states the decrease
/// before the value is used (vcgen.coma), and the query has no declaration for
/// the function, so the encoder would read the call at a guessed sort and
/// demote the proof. Dropping a hypothesis only removes what the proof may use.
fn reads_own_value(condition: &PureExpr, own_name: &str) -> bool {
    condition.any_recursive(|node| {
        matches!(node, PureExpr::LogicFnCall { name, .. }
            if name.rsplit("::").next() == Some(own_name))
    })
}

/// Range goals for the actual arguments passed to machine-integer parameters.
/// A width list that is not parallel to `args` (only possible for an arity
/// mismatch, rejected earlier) states no goal.
fn argument_range_goals(
    callee_param_int_widths: &[Option<MachineIntWidth>],
    args: &[PureExpr],
) -> Vec<PureExpr> {
    if callee_param_int_widths.len() != args.len() {
        return Vec::new();
    }
    args.iter()
        .zip(callee_param_int_widths)
        .filter_map(|(arg, width)| width.map(|w| machine_int_range(arg, w)))
        .flatten()
        .collect()
}

/// Present every integer disequality in the variant obligation's hypotheses as
/// its explicit order split.
///
/// On the integers `a != b`, `a < b or b < a`, and `a <= b - 1 or b <= a - 1`
/// are the SAME predicate, so this is a change of presentation and nothing
/// else — the hypothesis set before and after has exactly the same models.
///
/// Why it is needed. A variant edge like `is_even(n) -> is_odd(n - 1)` gives
/// the obligation `0 <= n, n != 0 |- 0 <= n - 1`. Its refutation needs INTEGER
/// reasoning: over the rationals `0 < n < 1` satisfies the negation, so no
/// Farkas certificate over the raw literals exists, and `ay` closes it with a
/// natively-validated `BvLiaTautology` lemma that has no checkable Alethe wire
/// rule. The step ships as a hole and the strict gate withholds the (correct)
/// `unsat` — surfacing as `variant obligation returned unknown: proof-trusted`.
/// The `<= b - 1` spelling does the integer strengthening in the FORMULA, where
/// it is plainly justified, leaving each branch a pure rational Farkas step the
/// external checker re-runs (measured: `la_generic :args (1 1)` twice plus
/// `or_pos` and resolutions, zero holes).
///
/// The `- 1` strengthening is valid on Int and NOT on Real, so the rewrite is
/// gated on [`is_certainly_int_valued`], which admits only expressions built
/// from integer literals, explicitly `Int`-sorted variables, and integer
/// arithmetic. Anything else is left exactly as it was, so an unrecognized
/// hypothesis keeps today's behaviour (fail-closed: the edge stays unproven).
fn split_integer_disequality_hypotheses(
    hypotheses: &mut [PureExpr],
    param_sorts: &HashMap<&str, Option<&ExprSort>>,
) {
    for hypothesis in hypotheses.iter_mut() {
        *hypothesis = hypothesis.rewrite_bottom_up(|node| {
            integer_disequality_order_split(&node, param_sorts).unwrap_or(node)
        });
    }
}

/// `a != b` over Int, rewritten to `a <= b - 1 or b <= a - 1`; `None` for every
/// other node and for operands not certainly integer-valued.
fn integer_disequality_order_split(
    expr: &PureExpr,
    param_sorts: &HashMap<&str, Option<&ExprSort>>,
) -> Option<PureExpr> {
    let (lhs, rhs) = match expr {
        PureExpr::UnOp(UnOp::Not, inner) => match inner.as_ref() {
            PureExpr::BinOp(lhs, BinOp::Eq, rhs) => (lhs.as_ref(), rhs.as_ref()),
            _ => return None,
        },
        PureExpr::BinOp(lhs, BinOp::Ne, rhs) => (lhs.as_ref(), rhs.as_ref()),
        _ => return None,
    };
    if !is_certainly_int_valued(lhs, param_sorts) || !is_certainly_int_valued(rhs, param_sorts) {
        return None;
    }
    let below = |smaller: &PureExpr, larger: &PureExpr| {
        PureExpr::BinOp(
            Arc::new(smaller.clone()),
            BinOp::Le,
            Arc::new(PureExpr::BinOp(
                Arc::new(larger.clone()),
                BinOp::Sub,
                Arc::new(PureExpr::Int(1)),
            )),
        )
    };
    Some(PureExpr::BinOp(
        Arc::new(below(lhs, rhs)),
        BinOp::Or,
        Arc::new(below(rhs, lhs)),
    ))
}

/// Conservatively decide that an expression denotes an integer.
///
/// Deliberately syntactic and closed: integer literals, integer arithmetic, and
/// variables that resolve to `ExprSort::Int` — through their own annotation
/// first, then the enclosing logic fn's declared parameter sorts. A variable
/// that resolves to neither is REFUSED: the `- 1` strengthening in
/// [`integer_disequality_order_split`] is unsound on `Real`, so a maybe-Int
/// operand must not authorize it.
fn is_certainly_int_valued(
    expr: &PureExpr,
    param_sorts: &HashMap<&str, Option<&ExprSort>>,
) -> bool {
    match expr {
        PureExpr::Int(_) => true,
        PureExpr::Var(name, annotation) => {
            let sort = annotation
                .as_ref()
                .or_else(|| param_sorts.get(name.as_str()).copied().flatten());
            matches!(sort, Some(ExprSort::Int))
        }
        PureExpr::UnOp(UnOp::Neg, inner) => is_certainly_int_valued(inner, param_sorts),
        PureExpr::BinOp(lhs, BinOp::Add | BinOp::Sub | BinOp::Mul, rhs) => {
            is_certainly_int_valued(lhs, param_sorts) && is_certainly_int_valued(rhs, param_sorts)
        }
        // A length/cardinality call is `Int` by the same judgement that admits
        // it as a variant term at all, and the strengthening this authorizes is
        // needed by exactly the hypothesis such a variant produces: the
        // `len(c) != 0` guard on the recursive branch, whose refutation is
        // integer reasoning no rational Farkas certificate can carry.
        PureExpr::MethodCall {
            receiver: _,
            method,
            args,
        } => args.is_empty() && ENCODER_INT_SORTED_NULLARY_METHODS.contains(&method.as_str()),
        _ => false,
    }
}

fn ensure_supported_int_variant(
    expr: &PureExpr,
    params: &[String],
    param_sort_hints: &[Option<ExprSort>],
    full_path: &str,
) -> Result<(), VariantError> {
    let param_sorts = param_sort_map(params, param_sort_hints);
    ensure_supported_int_variant_expr(expr, &param_sorts, full_path)
}

fn param_sort_map<'a>(
    params: &'a [String],
    param_sort_hints: &'a [Option<ExprSort>],
) -> HashMap<&'a str, Option<&'a ExprSort>> {
    params
        .iter()
        .zip(param_sort_hints.iter())
        .map(|(name, sort)| (name.as_str(), sort.as_ref()))
        .collect()
}

/// Nullary logic methods the ay encoder sorts `Int` UNCONDITIONALLY: its
/// method-call sort inference lists them in the arm that answers before any
/// receiver is consulted, and its receiver-propagation arm excludes them by
/// name, so no receiver shape can move the answer (pinned by
/// `test_method_len_infers_int`). They are the length/cardinality family —
/// `Int` on `Seq`, `FSet`, `FMap` and `String` alike, and in Creusot the
/// `seq.Seq` / `set.Fset` theory functions the oracle's
/// `well_founded_relation_Int` is applied to.
///
/// WHY A SORT JUDGEMENT AND NOT A NODE KIND. `0 <= before` together with
/// `after < before` is a well-founded order on the integers and on nothing
/// else, so what the gate must know is the sort the decrease goal will be
/// STATED over. Admitting a call whose sort that same encoder decides from its
/// receiver, or from a fallback, would make the order a guess — and a guessed
/// well-founded order is a termination credit nobody owes. Granting and owing
/// stay the same code in the same environment: the symbol admitted here is the
/// symbol the encoder gives `Sort::Int` inside the very query
/// `prove_self_variant_decrease` builds.
const ENCODER_INT_SORTED_NULLARY_METHODS: &[&str] = &["len", "len_logic"];

/// A subterm the decrease goal carries as an opaque value (the receiver of an
/// admitted length call).
///
/// Its own sort states nothing — only the admitted call's RESULT sort states
/// the order — so this is not an integer check. What it must guarantee is that
/// the term survives `PureExpr::substitute` and reaches the encoder as a plain
/// term: a binder or a control-flow form could capture the actual argument
/// substituted into it, and the variant would then measure a different value
/// after the call than before it. Those shapes are refused, never approximated.
fn ensure_variant_opaque_term(expr: &PureExpr, full_path: &str) -> Result<(), VariantError> {
    let refuse = || {
        Err(VariantError::UnsupportedIntSyntax {
            full_path: full_path.to_string(),
        })
    };
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => Ok(()),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => ensure_variant_opaque_term(inner, full_path),
        PureExpr::BinOp(lhs, _, rhs) => {
            ensure_variant_opaque_term(lhs, full_path)?;
            ensure_variant_opaque_term(rhs, full_path)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            ensure_variant_opaque_term(cond, full_path)?;
            ensure_variant_opaque_term(then_expr, full_path)?;
            ensure_variant_opaque_term(else_expr, full_path)
        }
        PureExpr::MethodCall {
            receiver,
            method: _,
            args,
        } => {
            ensure_variant_opaque_term(receiver, full_path)?;
            args.iter()
                .try_for_each(|arg| ensure_variant_opaque_term(arg, full_path))
        }
        PureExpr::LogicFnCall { name: _, args } => args
            .iter()
            .try_for_each(|arg| ensure_variant_opaque_term(arg, full_path)),
        _ => refuse(),
    }
}

fn ensure_supported_int_variant_expr(
    expr: &PureExpr,
    param_sorts: &HashMap<&str, Option<&ExprSort>>,
    full_path: &str,
) -> Result<(), VariantError> {
    match expr {
        PureExpr::Int(_) => Ok(()),
        PureExpr::Var(name, annotation) => {
            let sort = annotation
                .as_ref()
                .or_else(|| param_sorts.get(name.as_str()).copied().flatten());
            if is_supported_int_sort(sort) {
                Ok(())
            } else {
                Err(VariantError::NotIntegerValued {
                    full_path: full_path.to_string(),
                })
            }
        }
        PureExpr::UnOp(UnOp::Neg, inner) => {
            ensure_supported_int_variant_expr(inner, param_sorts, full_path)
        }
        PureExpr::BinOp(
            lhs,
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::DivTrunc
            | BinOp::RemTrunc,
            rhs,
        ) => {
            ensure_supported_int_variant_expr(lhs, param_sorts, full_path)?;
            ensure_supported_int_variant_expr(rhs, param_sorts, full_path)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            ensure_supported_bool_condition(cond, param_sorts, full_path)?;
            ensure_supported_int_variant_expr(then_expr, param_sorts, full_path)?;
            ensure_supported_int_variant_expr(else_expr, param_sorts, full_path)
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => ensure_supported_int_variant_expr(inner, param_sorts, full_path),
        // A length/cardinality call: Creusot's own variants are ordinary
        // pearlite terms resolved through the `WellFounded` impl of the term's
        // TYPE, so the discriminator here is the result sort, not the node
        // kind. Arguments would make this some other `len`; the modelled one
        // takes none.
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if args.is_empty() && ENCODER_INT_SORTED_NULLARY_METHODS.contains(&method.as_str()) => {
            ensure_variant_opaque_term(receiver, full_path)
        }
        PureExpr::Let { body, .. } => {
            ensure_supported_int_variant_expr(body, param_sorts, full_path)
        }
        _ => Err(VariantError::UnsupportedIntSyntax {
            full_path: full_path.to_string(),
        }),
    }
}

fn ensure_supported_bool_condition(
    expr: &PureExpr,
    param_sorts: &HashMap<&str, Option<&ExprSort>>,
    full_path: &str,
) -> Result<(), VariantError> {
    match expr {
        PureExpr::Bool(_) => Ok(()),
        PureExpr::Var(name, annotation) => {
            let sort = annotation
                .as_ref()
                .or_else(|| param_sorts.get(name.as_str()).copied().flatten());
            if matches!(sort, Some(ExprSort::Bool)) {
                Ok(())
            } else {
                Err(VariantError::UnsupportedBoolSyntax {
                    full_path: full_path.to_string(),
                })
            }
        }
        PureExpr::UnOp(UnOp::Not, inner) => {
            ensure_supported_bool_condition(inner, param_sorts, full_path)
        }
        PureExpr::BinOp(lhs, BinOp::And | BinOp::Or, rhs) => {
            ensure_supported_bool_condition(lhs, param_sorts, full_path)?;
            ensure_supported_bool_condition(rhs, param_sorts, full_path)
        }
        PureExpr::BinOp(
            lhs,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge,
            rhs,
        ) => {
            ensure_supported_int_variant_expr(lhs, param_sorts, full_path)?;
            ensure_supported_int_variant_expr(rhs, param_sorts, full_path)
        }
        _ => Err(VariantError::UnsupportedControlFlow {
            full_path: full_path.to_string(),
        }),
    }
}

fn is_supported_int_sort(sort: Option<&ExprSort>) -> bool {
    match sort {
        None | Some(ExprSort::Int) => true,
        // The unbounded logic integer `Int` (trust_wp_std / creusot_std) is
        // carried as an ADT sort by `ty_to_expr_sort_enriched`, but it IS the
        // mathematical integer the decrease obligation is stated over
        // (bug/1204 `evil(x: Int)`).
        Some(ExprSort::Datatype(id)) if is_logic_int_datatype_name(&resolve_sort_name(*id)) => true,
        Some(
            ExprSort::Bool
            | ExprSort::Seq
            | ExprSort::Unit
            | ExprSort::Datatype(_)
            | ExprSort::FMap
            | ExprSort::Tuple(_)
            | ExprSort::Ref(_)
            | ExprSort::MutRef(_)
            | ExprSort::TypeParam(_)
            | ExprSort::Float(_),
        ) => false,
        Some(_) => false,
    }
}

#[allow(clippy::similar_names)] // caller/callee prefixes are domain-distinct
fn prove_mutual_variant_decrease(
    caller_variant: &PureExpr,
    caller_requires: &[PureExpr],
    caller_params: &[String],
    caller_param_sort_hints: &[Option<ExprSort>],
    callee_variant: &PureExpr,
    callee_params: &[String],
    callee_param_int_widths: &[Option<MachineIntWidth>],
    edge: &LogicCallEdge,
) -> Result<(), VariantError> {
    if callee_params.len() != edge.actual_args.len() {
        return Err(VariantError::ArityMismatch {
            expected: callee_params.len(),
            actual: edge.actual_args.len(),
        });
    }

    let mut substitutions = HashMap::new();
    for (param, arg) in callee_params.iter().zip(edge.actual_args.iter()) {
        substitutions.insert(param.clone(), arg.clone());
    }

    let before = caller_variant.clone();
    let after = callee_variant.substitute(&substitutions);
    let mut ensures = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Int(0)),
            BinOp::Le,
            Arc::new(before.clone()),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Int(0)),
            BinOp::Le,
            Arc::new(after.clone()),
        ),
        PureExpr::BinOp(Arc::new(after), BinOp::Lt, Arc::new(before)),
    ];
    ensures.extend(argument_range_goals(
        callee_param_int_widths,
        &edge.actual_args,
    ));

    let mut requires = caller_requires.to_vec();
    requires.extend(edge.path_conditions.iter().cloned());
    split_integer_disequality_hypotheses(
        &mut requires,
        &param_sort_map(caller_params, caller_param_sort_hints),
    );
    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).track(Some(TrackLevel::Auto)),
    )
    .map_err(|error| VariantError::EncodingFailed {
        reason: error.to_string(),
    })?
    .apply_strict_trust(true);

    match result {
        VerificationResult::Verified(_) => Ok(()),
        VerificationResult::Assumed(_) => Err(VariantError::ObligationAssumed),
        VerificationResult::Failed(_) => Err(VariantError::ObligationFailed),
        VerificationResult::Unknown(reason) => Err(VariantError::ObligationUnknown {
            reason: reason.to_string(),
        }),
        _ => Err(VariantError::UnsupportedResult),
    }
}

/// ADT paths under which the unbounded logic integer `Int` is exposed.
fn is_logic_int_datatype_name(name: &str) -> bool {
    matches!(
        name,
        "trust_wp_std::logic::int::Int"
            | "trust_wp_std::logic::Int"
            | "trust_wp_std::Int"
            | "trust_wp::logic::int::Int"
            | "trust_wp::logic::Int"
            | "trust_wp::Int"
            | "creusot_std::Int"
            | "creusot_std::logic::Int"
    )
}

#[cfg(test)]
mod variant_grammar_tests {
    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn method(receiver: PureExpr, name: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: name.to_string(),
            args,
        }
    }

    fn check(expr: &PureExpr) -> Result<(), VariantError> {
        ensure_supported_int_variant(expr, &["c".to_string()], &[Some(ExprSort::Seq)], "t::f")
    }

    #[test]
    fn length_call_is_an_admitted_variant_term() {
        assert!(check(&method(var("c"), "len", vec![])).is_ok());
    }

    #[test]
    fn length_call_under_arithmetic_is_admitted() {
        let expr = PureExpr::BinOp(
            Arc::new(method(PureExpr::View(Arc::new(var("c"))), "len", vec![])),
            BinOp::Sub,
            Arc::new(var("i")),
        );
        assert!(check(&expr).is_ok());
    }

    #[test]
    fn a_call_the_encoder_does_not_sort_int_is_refused() {
        // `tail` is Seq-sorted; admitting it would state the decrease over an
        // order that is not well-founded below zero.
        assert!(matches!(
            check(&method(var("c"), "tail", vec![])),
            Err(VariantError::UnsupportedIntSyntax { .. })
        ));
    }

    #[test]
    fn an_argument_bearing_call_of_the_same_name_is_refused() {
        assert!(matches!(
            check(&method(var("c"), "len", vec![PureExpr::Int(0)])),
            Err(VariantError::UnsupportedIntSyntax { .. })
        ));
    }

    #[test]
    fn a_binder_inside_the_receiver_is_refused() {
        let receiver = PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Bool(true)),
            triggers: vec![],
        };
        assert!(matches!(
            check(&method(receiver, "len", vec![])),
            Err(VariantError::UnsupportedIntSyntax { .. })
        ));
    }

    #[test]
    fn a_length_disequality_hypothesis_is_split_into_its_order_cases() {
        let len = method(var("c"), "len", vec![]);
        let mut hypotheses = vec![PureExpr::UnOp(
            UnOp::Not,
            Arc::new(PureExpr::BinOp(
                Arc::new(len),
                BinOp::Eq,
                Arc::new(PureExpr::Int(0)),
            )),
        )];
        split_integer_disequality_hypotheses(&mut hypotheses, &HashMap::new());
        assert!(matches!(hypotheses[0], PureExpr::BinOp(_, BinOp::Or, _)));
    }
}
