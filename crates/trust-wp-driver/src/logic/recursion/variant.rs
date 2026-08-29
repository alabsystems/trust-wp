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
    formula::{BinOp, ExprSort, PureExpr, UnOp},
    TrackLevel,
};

use super::{
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
    /// The variant and/or the self-call edges are outside the supported integer
    /// fragment (non-Int variant, method/struct/`Self::`-dispatch variant,
    /// match/quantifier/closure-scoped recursion, text-only edges, parse-failed
    /// body, or arity mismatch). The caller must FALL BACK to its prior
    /// heuristics; it must NOT newly reject, to avoid regressing the many
    /// should_succeed logic fns whose variants live outside this fragment
    /// (e.g. spans::quux `i.0@`, spans::find_ptr_in_seq `s.len()-i`,
    /// bug/vcgen::set_max `s.len()`, list_reversal_lasso::pigeon via `Self::`).
    Unsupported,
    /// Every supported self-edge was proven to strictly decrease the variant.
    Proven,
    /// At least one supported self-edge could not be proven to decrease the
    /// variant; the solver returned a definitive `Failed`. This is a genuine
    /// termination-soundness rejection.
    Failed(String),
}

/// Attempt to discharge the per-edge variant-decrease obligation for the single
/// self-recursive node `idx` using the SMT backend.
///
/// Soundness/regression contract:
/// - Returns `Unsupported` unless the variant is a supported integer expression
///   AND there is at least one fully-structured self-edge AND *every* structured
///   self-edge is supported (no `unsupported_reason`, not text-only, arity
///   matches). Any incompleteness => `Unsupported` (fall back, never reject),
///   because proving decrease on a partial edge set would be unsound and
///   rejecting an unsupported-but-legitimate variant would regress
///   should_succeed.
/// - Returns `Proven` only when *all* supported structured self-edges discharge.
/// - Returns `Failed` only on a definitive solver `Failed`. `Unknown`/`Assumed`/
///   encoding errors are treated as `Unsupported` (fall back) so a hard solver
///   does not regress a legitimate-but-difficult case; the genuine
///   non-decrease cases in the corpus (incorrect_variant.rs) fail definitively.
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
        return SelfVariantDecrease::Unsupported;
    }
    if !node.variant_parse_errors.is_empty() {
        return SelfVariantDecrease::Unsupported;
    }
    if node.raw_variants.len() != 1 || node.parsed_variants.len() != 1 {
        return SelfVariantDecrease::Unsupported;
    }

    let variant = &node.parsed_variants[0];
    if ensure_supported_int_variant(
        variant,
        &node.params,
        &node.param_sort_hints,
        &node.full_path,
    )
    .is_err()
    {
        return SelfVariantDecrease::Unsupported;
    }

    // There must be a self-edge in the graph at all.
    if !graph
        .get(&idx)
        .is_some_and(|callees| callees.contains(&idx))
    {
        return SelfVariantDecrease::Unsupported;
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
        // incomplete (or the call is a method/dispatch form). Fall back.
        return SelfVariantDecrease::Unsupported;
    }

    // Every structured self-edge must be inside the supported fragment.
    for edge in &structured {
        if edge.unsupported_reason.is_some() {
            return SelfVariantDecrease::Unsupported;
        }
        if edge.actual_args.len() != node.params.len() {
            return SelfVariantDecrease::Unsupported;
        }
    }

    // Discharge decrease for each supported structured self-edge.
    for edge in &structured {
        match prove_self_variant_decrease(
            variant,
            &node.requires,
            &node.params,
            &node.param_sort_hints,
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
            // Unknown / Assumed / encoding / unsupported-result: do NOT reject a
            // legitimate-but-hard case. Fall back to the caller's heuristics.
            Err(_) => return SelfVariantDecrease::Unsupported,
        }
    }

    SelfVariantDecrease::Proven
}

/// Prove that `variant[args] < variant` (well-founded on Int) at one self-call.
///
/// Mirrors Creusot's `well_founded_relation_Int(before, after) = before >= 0 &&
/// before > after` (creusot-std/src/logic/well_founded.rs:40) discharged under
/// the function's own #[requires] plus the call-site path conditions, with the
/// implicit Int-variant precondition `before >= 0` supplied as a hypothesis
/// (matching the `i >= 0 ->` guard Creusot emits on Int-variant logic fns;
/// see tests/should_succeed/simple_trigger.coma `M_id`). Because `before >= 0`
/// is both hypothesis and the first conjunct of the goal, the residual
/// obligation is `before > after`.
#[allow(clippy::similar_names)]
fn prove_self_variant_decrease(
    variant: &PureExpr,
    requires: &[PureExpr],
    params: &[String],
    param_sort_hints: &[Option<ExprSort>],
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

    // Goal: before >= 0 && after < before  (well_founded_relation_Int).
    let ensures = vec![
        nonneg_before.clone(),
        PureExpr::BinOp(Arc::new(after), BinOp::Lt, Arc::new(before)),
    ];

    // Hypotheses: own #[requires] + accumulated path conditions + the implicit
    // Int-variant precondition `before >= 0`.
    let mut hypotheses = requires.to_vec();
    hypotheses.extend(edge.path_conditions.iter().cloned());
    hypotheses.push(nonneg_before);
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
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod,
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
            | ExprSort::Float,
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
    let ensures = vec![
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
