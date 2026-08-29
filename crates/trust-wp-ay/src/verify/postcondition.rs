// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Postcondition negation helpers shared across verification paths.
//!
//! Extracted from `verify/mod.rs` to keep the root verification module focused
//! on shared surface re-exports and bootstrap helpers. (#1268)

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ay_dpll::api::Term;
use tracing::debug;
use trust_wp_core::{
    formula::{BinOp, Pattern, PureExpr, UnOp},
    logic::LogicMode,
};

use super::function::axiom_detection::{
    expr_contains_embedded_existential, expr_contains_embedded_universal, has_open_logic_fns,
    instantiate_embedded_existentials_with_body_witness, skolemize_negated_universal,
};
use crate::{
    encoder::{
        infer_expr_sort, is_definitely_non_bool,
        match_enc::{deref_collapse::collapse_deref_for_bound_vars, short_constructor_name},
        AYEncoder,
    },
    error::EncodingError,
};

/// Conjoin a non-empty vec of terms into a single term, negate it, and assert.
///
/// This is the core verification pattern: negate the conjunction of
/// postcondition/invariant terms and check for satisfiability.
/// Avoids wrapping a single term in `and_many` (#564 dedup).
fn assert_negated_conjunction(encoder: &mut AYEncoder, terms: Vec<Term>) {
    debug_assert!(
        !terms.is_empty(),
        "assert_negated_conjunction called with empty terms"
    );
    // Coerce non-Bool terms to Bool via coerce_bool_operand. (#994)
    let coerced: Vec<Term> = terms
        .into_iter()
        .map(|t| encoder.coerce_bool_operand(t))
        .collect();
    let conjoined = if coerced.len() == 1 {
        coerced
            .into_iter()
            .next()
            .expect("non-empty: guarded by len() == 1 check")
    } else {
        encoder.solver_mut().and_many(&coerced)
    };
    let negated = encoder.solver_mut().not(conjoined);
    encoder.assert_term(negated);
}

/// Negate a postcondition at the PureExpr level when it contains a top-level
/// existential quantifier.
///
/// ay's E-matching does not correctly handle `NOT(exists x. P(x))` — it
/// treats the existential as an opaque theory literal and instantiates the
/// body without flipping polarity. This function manually applies the De Morgan
/// transformation at the PureExpr level:
///
/// ```text
/// NOT(exists<x> P(x))  →  forall<x> NOT P(x)
/// NOT(exists<a> exists<b> P(a, b))  →  forall<a> forall<b> NOT P(a, b)
/// ```
///
/// For non-existential expressions, returns `None` (caller should use the
/// standard ay-level NOT).
pub(crate) fn negate_existential_postcondition(expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::Exists {
        var,
        var_sort,
        body,
        triggers,
    } = expr
    else {
        return None;
    };
    // Recursively handle nested existentials in the body.
    // Each nested exists becomes a nested forall after negation.
    let negated_body = if matches!(body.as_ref(), PureExpr::Exists { .. }) {
        negate_existential_postcondition(body)
            .expect("invariant: body is Exists (guard on line above), so recursive call always returns Some")
    } else {
        PureExpr::UnOp(UnOp::Not, body.clone())
    };
    Some(PureExpr::Forall {
        var: var.clone(),
        var_sort: var_sort.clone(),
        body: Arc::new(negated_body),
        triggers: triggers.clone(),
    })
}

fn instantiate_top_level_existential_with_trivial_witness(expr: &PureExpr) -> Option<PureExpr> {
    let mut bound_vars = Vec::new();
    let mut body = expr;
    while let PureExpr::Exists {
        var,
        var_sort,
        body: inner,
        ..
    } = body
    {
        bound_vars.push((var.as_str(), var_sort.as_ref()));
        body = inner;
    }
    if bound_vars.is_empty() {
        return None;
    }

    let bound_names: HashSet<&str> = bound_vars.iter().map(|(name, _)| *name).collect();
    let mut substitutions = HashMap::new();
    collect_direct_existential_witnesses(body, &bound_names, &mut substitutions);
    collect_additive_existential_witnesses(body, &bound_vars, &bound_names, &mut substitutions);

    if substitutions.is_empty() {
        return None;
    }

    // Binder-erasing (#125): `exists` binders := collected witnesses.
    let instantiated = simplify_trivial_arithmetic(&body.substitute_binder_erasing(&substitutions));
    is_trivially_true_postcondition(&instantiated).then_some(instantiated)
}

fn collect_direct_existential_witnesses(
    expr: &PureExpr,
    bound_names: &HashSet<&str>,
    substitutions: &mut HashMap<String, PureExpr>,
) {
    let _ = expr.any_recursive(|node| {
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = node else {
            return false;
        };
        if let Some((var, witness)) = direct_existential_witness(lhs, rhs, bound_names)
            .or_else(|| direct_existential_witness(rhs, lhs, bound_names))
        {
            substitutions.entry(var).or_insert(witness);
        }
        false
    });
}

fn direct_existential_witness(
    candidate_var: &PureExpr,
    candidate_witness: &PureExpr,
    bound_names: &HashSet<&str>,
) -> Option<(String, PureExpr)> {
    let PureExpr::Var(var, _) = candidate_var else {
        return None;
    };
    if !bound_names.contains(var.as_str()) || expr_mentions_any_var(candidate_witness, bound_names)
    {
        return None;
    }
    Some((var.clone(), candidate_witness.clone()))
}

fn collect_additive_existential_witnesses(
    expr: &PureExpr,
    bound_vars: &[(&str, Option<&trust_wp_core::formula::ExprSort>)],
    bound_names: &HashSet<&str>,
    substitutions: &mut HashMap<String, PureExpr>,
) {
    let _ = expr.any_recursive(|node| {
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = node else {
            return false;
        };
        if let Some(assignments) =
            additive_existential_witnesses(lhs, rhs, bound_vars, bound_names, substitutions)
                .or_else(|| {
                    additive_existential_witnesses(rhs, lhs, bound_vars, bound_names, substitutions)
                })
        {
            substitutions.extend(assignments);
        }
        false
    });
}

fn additive_existential_witnesses(
    sum_side: &PureExpr,
    target_side: &PureExpr,
    bound_vars: &[(&str, Option<&trust_wp_core::formula::ExprSort>)],
    bound_names: &HashSet<&str>,
    substitutions: &HashMap<String, PureExpr>,
) -> Option<HashMap<String, PureExpr>> {
    if expr_mentions_any_var(target_side, bound_names) {
        return None;
    }

    let mut terms = Vec::new();
    flatten_add_terms(sum_side, &mut terms);
    if terms.len() < 2 {
        return None;
    }
    let mut vars = Vec::new();
    for term in terms {
        let PureExpr::Var(name, _) = term else {
            return None;
        };
        if !bound_names.contains(name.as_str()) || substitutions.contains_key(name) {
            return None;
        }
        if !bound_var_is_int_like(bound_vars, name) || vars.iter().any(|seen| seen == name) {
            return None;
        }
        vars.push(name.clone());
    }

    let first = vars.first()?.clone();
    let mut assignments = HashMap::new();
    assignments.insert(first, target_side.clone());
    for var in vars.into_iter().skip(1) {
        assignments.insert(var, PureExpr::Int(0));
    }
    Some(assignments)
}

fn bound_var_is_int_like(
    bound_vars: &[(&str, Option<&trust_wp_core::formula::ExprSort>)],
    var: &str,
) -> bool {
    bound_vars.iter().any(|(name, sort)| {
        *name == var
            && sort.map_or(true, |sort| {
                matches!(sort, trust_wp_core::formula::ExprSort::Int)
            })
    })
}

fn flatten_add_terms<'a>(expr: &'a PureExpr, terms: &mut Vec<&'a PureExpr>) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
            flatten_add_terms(lhs, terms);
            flatten_add_terms(rhs, terms);
        }
        other => terms.push(other),
    }
}

fn expr_mentions_any_var(expr: &PureExpr, names: &HashSet<&str>) -> bool {
    expr.any_recursive(
        |node| matches!(node, PureExpr::Var(name, _) if names.contains(name.as_str())),
    )
}

fn simplify_trivial_arithmetic(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::BinOp(lhs, op, rhs) => {
            let lhs = simplify_trivial_arithmetic(lhs);
            let rhs = simplify_trivial_arithmetic(rhs);
            match (op, &lhs, &rhs) {
                (BinOp::Add, PureExpr::Int(0), _) => rhs,
                (BinOp::Add, _, PureExpr::Int(0)) => lhs,
                (BinOp::Add, PureExpr::Int(left), PureExpr::Int(right)) => {
                    PureExpr::Int(left + right)
                }
                (BinOp::Eq, _, _)
                    if crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
                        &lhs, &rhs,
                    ) =>
                {
                    PureExpr::Bool(true)
                }
                (BinOp::And, PureExpr::Bool(true), _) => rhs,
                (BinOp::And, _, PureExpr::Bool(true)) => lhs,
                (BinOp::And, PureExpr::Bool(false), _) | (BinOp::And, _, PureExpr::Bool(false)) => {
                    PureExpr::Bool(false)
                }
                _ => PureExpr::BinOp(Arc::new(lhs), *op, Arc::new(rhs)),
            }
        }
        PureExpr::UnOp(UnOp::Not, inner) => {
            let inner = simplify_trivial_arithmetic(inner);
            match inner {
                PureExpr::Bool(value) => PureExpr::Bool(!value),
                other => PureExpr::UnOp(UnOp::Not, Arc::new(other)),
            }
        }
        other => other.clone(),
    }
}

/// Check whether a postcondition expression is trivially true at the PureExpr
/// level, without encoding it through ay.
///
/// Returns `true` for patterns that are statically known to be true:
/// - Reflexive equalities: `x == x`, `f(a) == f(a)` (structurally identical sides)
/// - `Bool(true)` literals
/// - Implications with trivially-true consequents: `guard ==> (x == x)`
/// - Conjunctions of trivially-true clauses: `(a == a) && (b == b)`
/// - Quantifiers with trivially-true bodies: `forall<v> true_body`
///
/// This avoids encoding logic function calls that produce quantified axioms
/// ay-dpll cannot instantiate, which causes quantifier-unhandled results on
/// tests like bug/206.rs (`ensures(u(*a) == u(*a))`). (#2696)
pub(crate) fn is_trivially_true_postcondition(expr: &PureExpr) -> bool {
    !expr_contains_div_or_mod(expr)
        && !expr_contains_final_over_literal(expr)
        && is_trivially_true_postcondition_shape(expr)
}

pub(crate) fn is_trivially_true_postcondition_under_requires(
    expr: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    if expr_contains_final_over_literal(expr) {
        return false;
    }
    if !div_mod_safety_obligations_satisfied(expr, requires) {
        return false;
    }
    if is_trivially_true_postcondition_shape(expr) {
        return true;
    }
    is_trivially_true_shift_nonzero_shape(expr, requires)
}

/// ★ #125 fail-closed guard, mirroring 8d7bf70's
/// `refuse_prophecy_over_constant`: a `Final` wrapper whose operand is a
/// ground literal is the print of the driver's borrow-chain advance of a
/// borrowed place's constant value (`^p` rendered as `^<c>`), and two such
/// prints may denote DIFFERENT conflated prophecies (the `7 + 7 == 9`
/// conflation closed by #124). Legitimate binder-erased `^x [x := c]` shapes
/// are normalised to `c` at the substitution sites
/// (`PureExpr::substitute_binder_erasing`) and never reach here, so refusing
/// costs no licensed capability. This guard closes the routes that do not go
/// through the literal evaluators at all — most importantly the reflexive
/// `is_sort_agnostic_equal` arm, which would accept `^<c> == ^<c>`
/// structurally and let `verify/pipeline.rs` mark the slice `Verified(None)`
/// with NO SOLVE AT ALL.
fn expr_contains_final_over_literal(expr: &PureExpr) -> bool {
    // Strip same-state projections when inspecting the wrapper's core: the
    // encoder's wrapper distribution sinks `^(view c)` / `^(*c)` at the same
    // literal arm, and this layer has no distribution of its own.
    fn projection_core(mut expr: &PureExpr) -> &PureExpr {
        while let PureExpr::View(inner) | PureExpr::Old(inner) | PureExpr::Deref(inner) = expr {
            expr = inner;
        }
        expr
    }
    expr.any_recursive(|node| {
        matches!(
            node,
            PureExpr::Final(inner)
                if matches!(
                    projection_core(inner),
                    PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_)
                )
        )
    })
}

/// Recognize `(1 << shift) != 0` as trivially true when `requires` imply
/// `0 <= shift < W` for some `W` that fits the proof BV width (#5).
///
/// This complements the BV-absorption rewrite in
/// `simplify_logic_body_expr_under_requires_inner`: after `(A | M) & M`
/// is rewritten to `M`, the set-bit postcondition's negated form collapses
/// to `(1 << bit) != 0`, which we can discharge purely from the integer
/// precondition `bit < USIZE_BITS`.
fn is_trivially_true_shift_nonzero_shape(expr: &PureExpr, requires: &[PureExpr]) -> bool {
    use trust_wp_core::formula::BinOp;
    // Match `mask != 0` or `0 != mask`, recursing through trivially-true
    // wrappers handled elsewhere is unnecessary because the caller already
    // applied the requires-aware simplifier.
    let PureExpr::BinOp(lhs, BinOp::Ne, rhs) = expr else {
        return false;
    };
    let mask = match (lhs.as_ref(), rhs.as_ref()) {
        (mask, PureExpr::Int(0)) => mask,
        (PureExpr::Int(0), mask) => mask,
        _ => return false,
    };
    let PureExpr::BinOp(one, BinOp::Shl, shift) = mask else {
        return false;
    };
    if !matches!(one.as_ref(), PureExpr::Int(1)) {
        return false;
    }
    shift_known_in_proof_range(shift, requires)
}

/// Return true when `requires` imply `0 <= shift` AND `shift < W` for some
/// positive `W` no larger than the BV proof width (64). Bounds may apply to
/// the bare shift expression OR to its `View(...)` wrapper (the driver
/// normalizes integer-typed unsigned arguments through `view`; e.g., the
/// `bit@ < USIZE_BITS@` precondition surfaces as `View(bit) < View(64)`).
fn shift_known_in_proof_range(shift: &PureExpr, requires: &[PureExpr]) -> bool {
    const PROOF_BV_WIDTH: i64 = 64;
    use trust_wp_core::formula::BinOp;
    let candidates = [shift.clone(), PureExpr::View(Arc::new(shift.clone()))];
    candidates.iter().any(|candidate| {
        let nonneg = PureExpr::BinOp(
            Arc::new(PureExpr::Int(0)),
            BinOp::Le,
            Arc::new(candidate.clone()),
        );
        let below_width = PureExpr::BinOp(
            Arc::new(candidate.clone()),
            BinOp::Lt,
            Arc::new(PureExpr::Int(PROOF_BV_WIDTH)),
        );
        requires_imply_expr(&nonneg, requires) && requires_imply_expr(&below_width, requires)
    })
}

fn is_trivially_true_postcondition_shape(expr: &PureExpr) -> bool {
    use trust_wp_core::formula::BinOp;
    if matches!(eval_bool_literal_expr(expr), Some(true)) {
        return true;
    }
    match expr {
        // Reflexive equality: lhs == rhs where both sides are structurally identical.
        // Uses sort-agnostic comparison (#2673) because the driver may attach different
        // ExprSort annotations to syntactically identical expressions.
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => {
            crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(lhs, rhs)
        }
        // Bool literal true
        PureExpr::Bool(true) => true,
        // Implication: guard ==> consequent — true if consequent is trivially true
        PureExpr::BinOp(_, BinOp::Implies, consequent) => {
            is_trivially_true_postcondition_shape(consequent)
        }
        // Conjunction: both sides must be trivially true
        PureExpr::BinOp(left, BinOp::And, right) => {
            is_trivially_true_postcondition_shape(left)
                && is_trivially_true_postcondition_shape(right)
        }
        // Ite: both branches trivially true
        PureExpr::Ite(_, then_br, else_br) => {
            is_trivially_true_postcondition_shape(then_br)
                && is_trivially_true_postcondition_shape(else_br)
        }
        // Quantifiers with trivially-true bodies
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            is_trivially_true_postcondition_shape(body)
        }
        // LetAssume: assumption adds context but body determines truth value.
        // If body is trivially true, the whole expression is trivially true
        // regardless of the assumption. (#2700)
        PureExpr::LetAssume { body, .. } => is_trivially_true_postcondition_shape(body),
        // LetObligation: obligation is conjoined with body. Both must be
        // trivially true for the whole to be trivially true. (#2700)
        PureExpr::LetObligation { obligation, body } => {
            is_trivially_true_postcondition_shape(obligation)
                && is_trivially_true_postcondition_shape(body)
        }
        _ => false,
    }
}

fn div_mod_safety_obligations_satisfied(expr: &PureExpr, requires: &[PureExpr]) -> bool {
    let mut ok = true;
    expr.for_each_recursive(|node| {
        if !ok {
            return;
        }
        if let PureExpr::BinOp(
            _,
            BinOp::Div | BinOp::Mod | BinOp::DivTrunc | BinOp::RemTrunc,
            divisor,
        ) = node
        {
            ok = divisor_known_nonzero_under_requires(divisor, requires);
        }
    });
    ok
}

fn divisor_known_nonzero_under_requires(divisor: &PureExpr, requires: &[PureExpr]) -> bool {
    if eval_int_literal_expr(divisor).is_some_and(|value| value != 0) {
        return true;
    }

    let normalized = normalize_result_logic_body_expr(divisor);
    let candidates = [
        divisor.clone(),
        normalized.clone(),
        PureExpr::View(Arc::new(normalized)),
    ];

    candidates.iter().any(|candidate| {
        let nonzero = PureExpr::BinOp(
            Arc::new(candidate.clone()),
            BinOp::Ne,
            Arc::new(PureExpr::Int(0)),
        );
        let equals_zero = PureExpr::BinOp(
            Arc::new(candidate.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        );
        requires_imply_expr(&nonzero, requires)
            || requires_imply_expr_false(&equals_zero, requires)
            || requires_imply_expr(
                &PureExpr::BinOp(
                    Arc::new(candidate.clone()),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(0)),
                ),
                requires,
            )
            || requires_imply_expr(
                &PureExpr::BinOp(
                    Arc::new(candidate.clone()),
                    BinOp::Lt,
                    Arc::new(PureExpr::Int(0)),
                ),
                requires,
            )
    })
}

fn expr_contains_div_or_mod(expr: &PureExpr) -> bool {
    use trust_wp_core::formula::BinOp;

    let mut found = false;
    expr.for_each_recursive(|node| {
        if found {
            return;
        }
        if matches!(
            node,
            PureExpr::BinOp(
                _,
                BinOp::Div | BinOp::Mod | BinOp::DivTrunc | BinOp::RemTrunc,
                _
            )
        ) {
            found = true;
        }
    });
    found
}

fn result_equals_return_expr_via_logic_body(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    return_expr: Option<&PureExpr>,
) -> bool {
    result_equals_return_expr_via_logic_body_with_requires(ensure, logic_fns, return_expr, &[])
}

pub(crate) fn result_postcondition_matches_return_expr(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    let Some(return_expr) = return_expr else {
        return false;
    };
    if super::expr_contains_result_var(ensure) {
        let mut result_substitution = HashMap::new();
        result_substitution.insert("result".to_string(), return_expr.clone());
        let goal = ensure.substitute(&result_substitution);
        let goal =
            simplify_logic_body_expr_under_requires(&normalize_entailment_expr(&goal), requires);
        if is_trivially_true_postcondition_under_requires(&goal, requires) {
            return true;
        }
    }
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = ensure else {
        return false;
    };
    let expected = match (lhs.as_ref(), rhs.as_ref()) {
        (PureExpr::Var(name, _), expected) if name == "result" => expected,
        (expected, PureExpr::Var(name, _)) if name == "result" => expected,
        _ => return false,
    };
    let expected = simplify_logic_body_expr_under_requires(
        &normalize_result_logic_body_expr(expected),
        requires,
    );
    let return_expr = simplify_logic_body_expr_under_requires(
        &normalize_result_logic_body_expr(return_expr),
        requires,
    );
    if !div_mod_safety_obligations_satisfied(&expected, requires)
        || !div_mod_safety_obligations_satisfied(&return_expr, requires)
    {
        return false;
    }
    logic_body_exprs_equal(&expected, &return_expr)
}

pub(crate) fn result_postcondition_matches_return_expr_via_logic_bodies(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    let (Some(logic_fns), Some(return_expr)) = (logic_fns, return_expr) else {
        return false;
    };
    let mut result_substitution = HashMap::new();
    result_substitution.insert("result".to_string(), return_expr.clone());
    let goal = ensure.substitute(&result_substitution);
    let goal = inline_logic_fn_calls_from_defs_under_requires(&goal, logic_fns, requires);
    let goal = simplify_logic_body_expr_under_requires(&normalize_entailment_expr(&goal), requires);
    is_trivially_true_postcondition_under_requires(&goal, requires)
}

pub(crate) fn result_postcondition_contradicts_return_expr_via_logic_bodies(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    if !super::expr_contains_result_var(ensure) {
        return false;
    }
    let (Some(logic_fns), Some(return_expr)) = (logic_fns, return_expr) else {
        return false;
    };
    let mut result_substitution = HashMap::new();
    result_substitution.insert("result".to_string(), return_expr.clone());
    let goal = ensure.substitute(&result_substitution);
    let goal = inline_logic_fn_calls_from_defs_under_requires(&goal, logic_fns, requires);
    let goal = simplify_logic_body_expr_under_requires(&normalize_entailment_expr(&goal), requires);
    is_definitely_false_postcondition(&goal)
}

pub(crate) fn result_postcondition_contradicts_return_expr(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    if !super::expr_contains_result_var(ensure) {
        return false;
    }
    let Some(return_expr) = return_expr else {
        return false;
    };
    let mut result_substitution = HashMap::new();
    result_substitution.insert("result".to_string(), return_expr.clone());
    let goal = ensure.substitute(&result_substitution);
    let goal = simplify_logic_body_expr_under_requires(&normalize_entailment_expr(&goal), requires);
    if postcondition_contradicts_requirements(&goal, requires) {
        return true;
    }
    is_definitely_false_postcondition(&goal)
}

pub(crate) fn postcondition_contradicts_requirements(
    ensure: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    let PureExpr::BinOp(ensure_left, BinOp::Eq, ensure_right) = ensure else {
        return false;
    };
    requires.iter().any(|require| {
        let mut conjuncts = Vec::new();
        collect_top_level_conjuncts(require, &mut conjuncts);
        conjuncts.into_iter().any(|conjunct| {
            let PureExpr::BinOp(require_left, BinOp::Eq, require_right) = conjunct else {
                return false;
            };
            equality_sides_contradict(ensure_left, ensure_right, require_left, require_right)
        })
    })
}

fn equality_sides_contradict(
    ensure_left: &PureExpr,
    ensure_right: &PureExpr,
    require_left: &PureExpr,
    require_right: &PureExpr,
) -> bool {
    if linear_equalities_contradict(ensure_left, ensure_right, require_left, require_right) {
        return true;
    }
    if literal_equalities_contradict(ensure_left, ensure_right, require_left, require_right) {
        return true;
    }
    let exprs_equal = crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal;
    (exprs_equal(ensure_left, require_left)
        && affine_equalities_contradict(ensure_right, require_right))
        || (exprs_equal(ensure_left, require_right)
            && affine_equalities_contradict(ensure_right, require_left))
        || (exprs_equal(ensure_right, require_left)
            && affine_equalities_contradict(ensure_left, require_right))
        || (exprs_equal(ensure_right, require_right)
            && affine_equalities_contradict(ensure_left, require_left))
}

fn literal_equalities_contradict(
    ensure_left: &PureExpr,
    ensure_right: &PureExpr,
    require_left: &PureExpr,
    require_right: &PureExpr,
) -> bool {
    let exprs_equal = crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal;
    (exprs_equal(ensure_left, require_left)
        && literal_values_contradict(ensure_right, require_right))
        || (exprs_equal(ensure_left, require_right)
            && literal_values_contradict(ensure_right, require_left))
        || (exprs_equal(ensure_right, require_left)
            && literal_values_contradict(ensure_left, require_right))
        || (exprs_equal(ensure_right, require_right)
            && literal_values_contradict(ensure_left, require_left))
}

fn literal_values_contradict(left: &PureExpr, right: &PureExpr) -> bool {
    if let (Some(left), Some(right)) = (eval_bool_literal_expr(left), eval_bool_literal_expr(right))
    {
        return left != right;
    }
    if let (Some(left), Some(right)) = (eval_int_literal_expr(left), eval_int_literal_expr(right)) {
        return left != right;
    }
    false
}

fn affine_equalities_contradict(left: &PureExpr, right: &PureExpr) -> bool {
    let (Some((left_base, left_offset)), Some((right_base, right_offset))) = (
        affine_expr_base_offset(left),
        affine_expr_base_offset(right),
    ) else {
        return false;
    };
    left_offset != right_offset && logic_body_exprs_equal(left_base, right_base)
}

#[derive(Clone, Debug)]
struct LinearExpr {
    terms: Vec<(PureExpr, i64)>,
    constant: i64,
}

impl LinearExpr {
    fn constant(value: i64) -> Self {
        Self {
            terms: Vec::new(),
            constant: value,
        }
    }

    fn atom(expr: PureExpr) -> Self {
        Self {
            terms: vec![(expr, 1)],
            constant: 0,
        }
    }

    fn add_constant(&mut self, value: i64) -> Option<()> {
        self.constant = self.constant.checked_add(value)?;
        Some(())
    }

    fn add_term(&mut self, term: PureExpr, coeff: i64) -> Option<()> {
        if coeff == 0 {
            return Some(());
        }
        let exprs_equal = crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal;
        for index in 0..self.terms.len() {
            if exprs_equal(&self.terms[index].0, &term) {
                let next = self.terms[index].1.checked_add(coeff)?;
                if next == 0 {
                    self.terms.remove(index);
                } else {
                    self.terms[index].1 = next;
                }
                return Some(());
            }
        }
        self.terms.push((term, coeff));
        Some(())
    }

    fn add_scaled(&mut self, other: &Self, scale: i64) -> Option<()> {
        self.add_constant(other.constant.checked_mul(scale)?)?;
        for (term, coeff) in &other.terms {
            self.add_term(term.clone(), coeff.checked_mul(scale)?)?;
        }
        Some(())
    }

    fn scale(mut self, scale: i64) -> Option<Self> {
        self.constant = self.constant.checked_mul(scale)?;
        for (_, coeff) in &mut self.terms {
            *coeff = coeff.checked_mul(scale)?;
        }
        Some(self)
    }

    fn same_terms(&self, other: &Self) -> bool {
        if self.terms.len() != other.terms.len() {
            return false;
        }
        let exprs_equal = crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal;
        self.terms.iter().all(|(left_term, left_coeff)| {
            other.terms.iter().any(|(right_term, right_coeff)| {
                left_coeff == right_coeff && exprs_equal(left_term, right_term)
            })
        })
    }
}

fn linear_equalities_contradict(
    ensure_left: &PureExpr,
    ensure_right: &PureExpr,
    require_left: &PureExpr,
    require_right: &PureExpr,
) -> bool {
    let (Some(ensure), Some(require)) = (
        linear_equality_signature(ensure_left, ensure_right),
        linear_equality_signature(require_left, require_right),
    ) else {
        return false;
    };
    ensure.same_terms(&require) && ensure.constant != require.constant
}

fn linear_equality_signature(left: &PureExpr, right: &PureExpr) -> Option<LinearExpr> {
    let mut signature = linear_expr(left)?;
    signature.add_scaled(&linear_expr(right)?, -1)?;
    Some(signature)
}

fn linear_expr(expr: &PureExpr) -> Option<LinearExpr> {
    match expr {
        PureExpr::Int(value) => Some(LinearExpr::constant(*value)),
        PureExpr::Var(_, _)
        | PureExpr::LogicFnCall { .. }
        | PureExpr::MethodCall { .. }
        | PureExpr::Old(_)
        | PureExpr::Deref(_)
        | PureExpr::Final(_)
        | PureExpr::View(_) => Some(LinearExpr::atom(expr.clone())),
        PureExpr::UnOp(UnOp::Neg, inner) => linear_expr(inner)?.scale(-1),
        PureExpr::BinOp(left, BinOp::Add, right) => {
            let mut result = linear_expr(left)?;
            result.add_scaled(&linear_expr(right)?, 1)?;
            Some(result)
        }
        PureExpr::BinOp(left, BinOp::Sub, right) => {
            let mut result = linear_expr(left)?;
            result.add_scaled(&linear_expr(right)?, -1)?;
            Some(result)
        }
        _ => None,
    }
}

fn is_definitely_false_postcondition(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Bool(false) => true,
        PureExpr::Bool(true) => false,
        PureExpr::UnOp(UnOp::Not, inner) => is_trivially_true_postcondition(inner),
        PureExpr::BinOp(left, BinOp::And, right) => {
            is_definitely_false_postcondition(left) || is_definitely_false_postcondition(right)
        }
        PureExpr::BinOp(left, BinOp::Or, right) => {
            is_definitely_false_postcondition(left) && is_definitely_false_postcondition(right)
        }
        PureExpr::BinOp(left, BinOp::Implies, right) => {
            is_trivially_true_postcondition(left) && is_definitely_false_postcondition(right)
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            if let (Some(left), Some(right)) =
                (eval_int_literal_expr(left), eval_int_literal_expr(right))
            {
                return left != right;
            }
            if let (Some(left), Some(right)) =
                (eval_bool_literal_expr(left), eval_bool_literal_expr(right))
            {
                return left != right;
            }
            if let (Some((left_base, left_offset)), Some((right_base, right_offset))) = (
                affine_expr_base_offset(left),
                affine_expr_base_offset(right),
            ) {
                return left_offset != right_offset
                    && logic_body_exprs_equal(left_base, right_base);
            }
            if let Some(signature) = linear_equality_signature(left, right) {
                return signature.terms.is_empty() && signature.constant != 0;
            }
            false
        }
        PureExpr::BinOp(left, BinOp::Ne, right) => logic_body_exprs_equal(left, right),
        PureExpr::BinOp(left, BinOp::Lt | BinOp::Gt, right) => logic_body_exprs_equal(left, right),
        PureExpr::BinOp(left, BinOp::Le, right) => {
            if let (Some(left), Some(right)) =
                (eval_int_literal_expr(left), eval_int_literal_expr(right))
            {
                return left > right;
            }
            false
        }
        PureExpr::BinOp(left, BinOp::Ge, right) => {
            if let (Some(left), Some(right)) =
                (eval_int_literal_expr(left), eval_int_literal_expr(right))
            {
                return left < right;
            }
            false
        }
        _ => false,
    }
}

fn affine_expr_base_offset(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    match expr {
        PureExpr::BinOp(left, BinOp::Add, right) => {
            if let Some(value) = eval_int_literal_expr(right) {
                let (base, offset) = affine_expr_base_offset(left)?;
                return Some((base, offset.checked_add(value)?));
            }
            if let Some(value) = eval_int_literal_expr(left) {
                let (base, offset) = affine_expr_base_offset(right)?;
                return Some((base, offset.checked_add(value)?));
            }
            None
        }
        PureExpr::BinOp(left, BinOp::Sub, right) => {
            let value = eval_int_literal_expr(right)?;
            let (base, offset) = affine_expr_base_offset(left)?;
            Some((base, offset.checked_sub(value)?))
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => affine_expr_base_offset(inner),
        PureExpr::Int(_) => None,
        _ => Some((expr, 0)),
    }
}

fn logic_fn_body_visible(logic_fn: &trust_wp_core::logic::LogicFnDef) -> bool {
    !logic_fn.is_opaque() && !logic_fn.is_recursive() && logic_fn.mode() != LogicMode::Default
}

fn logic_fn_body_available_under_requires(
    logic_fn: &trust_wp_core::logic::LogicFnDef,
    args: &[PureExpr],
    requires: &[PureExpr],
) -> bool {
    if !logic_fn_body_visible(logic_fn) || logic_fn.params().len() != args.len() {
        return false;
    }
    logic_fn_instantiated_requires_hold(logic_fn, args, requires)
}

fn logic_fn_instantiated_requires_hold(
    logic_fn: &trust_wp_core::logic::LogicFnDef,
    args: &[PureExpr],
    requires: &[PureExpr],
) -> bool {
    if logic_fn.requires().is_empty() {
        return true;
    }
    let substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    logic_fn.requires().iter().all(|require| {
        // Binder-erasing (#125): formals := call arguments.
        let instantiated = require.substitute_binder_erasing(&substitutions);
        let normalized = normalize_entailment_expr(&instantiated);
        let simplified = simplify_logic_body_expr_under_requires(&normalized, requires);
        is_trivially_true_postcondition(&simplified) || requires_imply_expr(&simplified, requires)
    })
}

pub(crate) fn result_equals_return_expr_via_logic_body_with_requires(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    let (Some(logic_fns), Some(return_expr)) = (logic_fns, return_expr) else {
        return false;
    };
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = ensure else {
        return false;
    };

    let logic_call = match (lhs.as_ref(), rhs.as_ref()) {
        (lhs, call) if is_result_selector(lhs) => call,
        (call, rhs) if is_result_selector(rhs) => call,
        _ => return false,
    };
    let PureExpr::LogicFnCall { name, args } = logic_call else {
        return false;
    };

    let Some(logic_fn) = logic_fns.iter().find(|f| {
        f.name() == name
            && f.params().len() == args.len()
            && logic_fn_body_available_under_requires(f, args, requires)
    }) else {
        return false;
    };

    let substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    // Binder-erasing (#125): formals := call arguments.
    let expanded = normalize_result_logic_body_expr(
        &logic_fn.body().substitute_binder_erasing(&substitutions),
    );
    let expanded = simplify_logic_body_expr_under_requires(&expanded, requires);
    let return_expr = simplify_logic_body_expr_under_requires(
        &normalize_result_logic_body_expr(return_expr),
        requires,
    );
    if !div_mod_safety_obligations_satisfied(&expanded, requires)
        || !div_mod_safety_obligations_satisfied(&return_expr, requires)
    {
        return false;
    }
    logic_body_exprs_equal(&expanded, &return_expr)
}

/// Recognise the result selector on either side of a postcondition equality.
///
/// Accepts a raw `Var("result")` plus any number of `View` wrappers (e.g. the
/// `result@` projection in `result@ == max_int(a@, b@)`). The explicit
/// method-call form `result.view()` is also accepted because it lowers to the
/// same `View` operation in the encoder (see
/// `encode_view_expr` dispatch for the `"view"` method). The body matcher
/// strips both forms via `normalize_result_logic_body_expr`, so the wrappers do
/// not alter the comparison — they only block the syntactic guard.
///
/// The explicit `result.deep_model()` form is likewise accepted: `deep_model` is
/// a deterministic conversion to the logical deep model, so it is a *function*
/// of its receiver. Stripping it from both sides of an equality preserves
/// soundness in the direction the matcher relies on — if the stripped sides
/// are equal as Rust values then by congruence the original `.deep_model()`
/// forms are equal as logical values. (#181_ident, Phase 3 B4)
///
/// The `Deref` wrapper (parsed from the Creusot `*result` form, encoding the
/// current value of a borrow) is also accepted on the same congruence grounds.
/// `Deref` is a deterministic projection — if its receivers are syntactically
/// equal after stripping, the original `*` forms are equal too. The strip is
/// purely a *matcher* operation: it only fires when the matcher would compare
/// syntactically identical PureExprs after normalization, so the resulting
/// postcondition equality is justified by congruence of `Deref` over equality.
/// (Phase 3 B4)
fn is_result_selector(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == "result",
        PureExpr::View(inner) => is_result_selector(inner),
        PureExpr::Deref(inner) => is_result_selector(inner),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if (method == "view" || method == "deep_model") && args.is_empty() => {
            is_result_selector(receiver)
        }
        _ => false,
    }
}

pub(crate) fn requirements_imply_postcondition_via_logic_bodies(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    let (Some(logic_fns), Some(return_expr)) = (logic_fns, return_expr) else {
        return false;
    };
    let mut result_substitution = HashMap::new();
    result_substitution.insert("result".to_string(), return_expr.clone());
    let goal = ensure.substitute(&result_substitution);
    let goal = normalize_entailment_expr(&inline_logic_fn_calls_from_defs_under_requires(
        &goal, logic_fns, requires,
    ));
    let normalized_requires: Vec<PureExpr> = requires
        .iter()
        .map(|require| {
            normalize_entailment_expr(&inline_logic_fn_calls_from_defs_under_requires(
                require, logic_fns, requires,
            ))
        })
        .collect();
    requirements_imply_normalized_expr(&goal, &normalized_requires)
}

pub(crate) fn postcondition_true_via_logic_bodies(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    let goal = normalize_entailment_expr(&inline_logic_fn_calls_from_defs(ensure, logic_fns));
    is_trivially_true_postcondition(&goal)
}

pub(crate) fn postcondition_false_via_logic_bodies(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    requires: &[PureExpr],
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    let goal = inline_logic_fn_calls_from_defs_under_requires(ensure, logic_fns, requires);
    let goal = simplify_logic_body_expr_under_requires(&normalize_entailment_expr(&goal), requires);
    is_definitely_false_postcondition(&goal)
}

pub(crate) fn logic_fn_equality_matches_body(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = ensure else {
        return false;
    };
    logic_fn_equality_orientation_matches_body(lhs, rhs, logic_fns)
        || logic_fn_equality_orientation_matches_body(rhs, lhs, logic_fns)
}

pub(crate) fn logic_fn_equality_has_visible_body_candidate(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = ensure else {
        return false;
    };
    logic_fn_equality_orientation_has_visible_body(lhs, rhs, logic_fns)
        || logic_fn_equality_orientation_has_visible_body(rhs, lhs, logic_fns)
}

/// Recognise `result@ == f(args)` where `f` is a non-recursive, non-opaque
/// logic function whose body is a pure finite-domain integer/bitwise expression
/// (the class the BV↔LIA enumeration bridge can decide), against a concrete
/// `return_expr`.
///
/// When this holds, the obligation `result@ == f(args)` is decidable by the
/// solver's bit-blast/enumeration bridge even though no *syntactic* body match
/// exists (e.g. popcount's `result@ == count8_log(n)`, where the SWAR body and
/// the per-bit ITE-sum compute the same function but are structurally
/// different). Such obligations should be routed to the solver rather than
/// short-circuited to `Unknown` by [`logic_fn_equality_has_visible_body_candidate`].
///
/// This is purely a ROUTING gate: it never asserts a result. Soundness rests
/// entirely on the solver/bridge, which requires UNSAT over the full finite
/// domain to prove the equality and reports a counterexample (Failed) for any
/// value that does not match — so an analogous wrong value (e.g.
/// `result@ == f(n) + 1`) stays unprovable.
pub(crate) fn logic_fn_equality_is_finite_enumerable_candidate(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    return_expr: Option<&PureExpr>,
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    // A concrete return expression is required: the solver binds `result` to it
    // and proves the equality against `f`'s inlined body.
    if return_expr.is_none() {
        return false;
    }
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = ensure else {
        return false;
    };
    finite_enumerable_orientation(lhs, rhs, logic_fns)
        || finite_enumerable_orientation(rhs, lhs, logic_fns)
}

/// Recognise `result == f(args)` where `f` is a non-recursive, non-opaque
/// logic fn whose body is a builtin collection index over a field projection
/// of a parameter — the shadowed-`IndexLogic` accessor class, e.g.
/// `impl IndexLogic<usize> for Memory { #[logic] fn index_logic(self, i) {
/// self.0[i] } }` (list_reversal_lasso).
///
/// Such a fn's global defining axiom IS asserted (non-recursive), and the
/// obligation reduces to a couple of ground select facts — cheap for the
/// solver. Route it to the solver instead of short-circuiting to `Unknown`
/// via [`logic_fn_equality_has_visible_body_candidate`].
///
/// Purely a ROUTING gate (mirrors
/// [`logic_fn_equality_is_finite_enumerable_candidate`]): it never asserts a
/// result; soundness rests entirely on the solver, which still needs a full
/// UNSAT to verify.
pub(crate) fn logic_fn_equality_is_projected_index_candidate(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = ensure else {
        return false;
    };
    projected_index_orientation(lhs, rhs, logic_fns)
        || projected_index_orientation(rhs, lhs, logic_fns)
}

fn projected_index_orientation(
    selector: &PureExpr,
    logic_call: &PureExpr,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
) -> bool {
    if !is_result_selector(selector) {
        return false;
    }
    let PureExpr::LogicFnCall { name, args } = logic_call else {
        return false;
    };
    logic_fns.iter().any(|logic_fn| {
        logic_fn.name() == name
            && logic_fn.params().len() == args.len()
            && logic_fn_body_visible(logic_fn)
            && !logic_fn.is_recursive()
            && !logic_fn.is_opaque()
            && logic_fn.requires().is_empty()
            && is_param_field_index_body(logic_fn.body(), logic_fn.params())
    })
}

/// Body shape `<field-projection of param>[<param>]`, optionally through `@`
/// views: a `MethodCall` builtin index whose receiver is a positional/named
/// field projection of a parameter and whose index argument is a parameter.
fn is_param_field_index_body(body: &PureExpr, params: &[String]) -> bool {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = body
    else {
        return false;
    };
    if !matches!(method.as_str(), "index_logic" | "index") || args.len() != 1 {
        return false;
    }
    is_param_field_projection(receiver, params) && is_param_atom(&args[0], params)
}

fn is_param_field_projection(expr: &PureExpr, params: &[String]) -> bool {
    use trust_wp_core::formula::internal::tuple_lowering::{
        NAMED_FIELD_LOGIC_FN_PREFIX, TUPLE_FIELD_LOGIC_FN_PREFIX,
    };
    match expr {
        PureExpr::View(inner) => is_param_field_projection(inner, params),
        PureExpr::LogicFnCall { name, args }
            if name.starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX)
                || name.starts_with(NAMED_FIELD_LOGIC_FN_PREFIX) =>
        {
            matches!(args.as_slice(), [inner] if is_param_atom(inner, params))
        }
        _ => false,
    }
}

fn is_param_atom(expr: &PureExpr, params: &[String]) -> bool {
    match expr {
        PureExpr::Var(name, _) => params.iter().any(|p| p == name),
        PureExpr::View(inner) | PureExpr::Deref(inner) => is_param_atom(inner, params),
        _ => false,
    }
}

fn finite_enumerable_orientation(
    selector: &PureExpr,
    logic_call: &PureExpr,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
) -> bool {
    if !is_result_selector(selector) {
        return false;
    }
    let PureExpr::LogicFnCall { name, args } = logic_call else {
        return false;
    };
    logic_fns.iter().any(|logic_fn| {
        logic_fn.name() == name
            && logic_fn.params().len() == args.len()
            && logic_fn_body_visible(logic_fn)
            && !logic_fn.is_recursive()
            && !logic_fn.is_opaque()
            && logic_fn.requires().is_empty()
            && is_finite_enumerable_int_body(logic_fn.body())
    })
}

/// Structural test for an integer-sorted expression the BV↔LIA enumeration
/// evaluator can interpret over a bounded domain: constants, variables, the
/// linear/bitwise integer operators, and `Ite` over comparisons. Any other node
/// (method calls, logic-fn calls, sequence/quantifier operators, casts to
/// non-integer domains, …) makes the body non-enumerable and disqualifies the
/// candidate, keeping the routing gate scoped to popcount-style obligations.
fn is_finite_enumerable_int_body(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(_) => true,
        PureExpr::Var(_, _) => true,
        PureExpr::BinOp(lhs, op, rhs) => {
            matches!(
                op,
                BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Mod
                    | BinOp::BitAnd
                    | BinOp::BitOr
                    | BinOp::BitXor
                    | BinOp::Shl
                    | BinOp::Shr
            ) && is_finite_enumerable_int_body(lhs)
                && is_finite_enumerable_int_body(rhs)
        }
        PureExpr::UnOp(UnOp::Neg | UnOp::BitNot, inner) => is_finite_enumerable_int_body(inner),
        PureExpr::Ite(cond, then_branch, else_branch) => {
            is_finite_enumerable_int_guard(cond)
                && is_finite_enumerable_int_body(then_branch)
                && is_finite_enumerable_int_body(else_branch)
        }
        _ => false,
    }
}

/// Comparison/boolean guards permitted inside an enumerable `Ite`.
fn is_finite_enumerable_int_guard(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Bool(_) => true,
        PureExpr::BinOp(lhs, op, rhs) => match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                is_finite_enumerable_int_body(lhs) && is_finite_enumerable_int_body(rhs)
            }
            BinOp::And | BinOp::Or => {
                is_finite_enumerable_int_guard(lhs) && is_finite_enumerable_int_guard(rhs)
            }
            _ => false,
        },
        PureExpr::UnOp(UnOp::Not, inner) => is_finite_enumerable_int_guard(inner),
        _ => false,
    }
}

pub(crate) fn recursive_logic_fn_equality_matches_evaluation(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = ensure else {
        return false;
    };
    let recursive_fns = visible_recursive_logic_fn_map(logic_fns, mode_overrides);
    if recursive_fns.is_empty() {
        return false;
    }
    let lhs =
        crate::encoder::try_evaluate_recursive(lhs, &recursive_fns, MAX_LOGIC_FN_INLINE_DEPTH);
    let rhs =
        crate::encoder::try_evaluate_recursive(rhs, &recursive_fns, MAX_LOGIC_FN_INLINE_DEPTH);
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => logic_body_exprs_equal(&lhs, &rhs),
        _ => false,
    }
}

pub(crate) fn recursive_postcondition_matches_evaluation_under_requires(
    ensure: &PureExpr,
    requires: &[PureExpr],
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    let recursive_fns = visible_recursive_logic_fn_map(logic_fns, mode_overrides);
    if recursive_fns.is_empty() {
        return false;
    }

    let substitutions = literal_equalities_from_requirements(requires);
    if substitutions.is_empty() {
        return false;
    }

    let substituted = crate::encoder::simplify_ground(&ensure.substitute(&substitutions));
    matches!(
        crate::encoder::try_evaluate_recursive(
            &substituted,
            &recursive_fns,
            MAX_LOGIC_FN_INLINE_DEPTH,
        ),
        Some(PureExpr::Bool(true))
    )
}

pub(crate) fn postcondition_contains_visible_recursive_logic_call(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    let recursive_fns = visible_recursive_logic_fn_map(logic_fns, mode_overrides);
    if recursive_fns.is_empty() {
        return false;
    }
    let recursive_names: HashSet<&str> = recursive_fns.keys().copied().collect();
    let mut found = false;
    ensure.for_each_recursive(|node| {
        if found {
            return;
        }
        if let PureExpr::LogicFnCall { name, .. } = node {
            found = recursive_names.contains(name.as_str());
        }
    });
    found
}

fn visible_recursive_logic_fn_map<'a>(
    logic_fns: &'a [trust_wp_core::logic::LogicFnDef],
    mode_overrides: Option<&[LogicMode]>,
) -> HashMap<&'a str, &'a trust_wp_core::logic::LogicFnDef> {
    logic_fns
        .iter()
        .enumerate()
        .filter_map(|(idx, logic_fn)| {
            let effective_mode = mode_overrides
                .and_then(|modes| modes.get(idx))
                .copied()
                .unwrap_or_else(|| logic_fn.mode());
            (logic_fn.is_recursive()
                && !logic_fn.is_opaque()
                && effective_mode != LogicMode::Default)
                .then_some((logic_fn.name(), logic_fn))
        })
        .collect()
}

fn literal_equalities_from_requirements(requires: &[PureExpr]) -> HashMap<String, PureExpr> {
    let mut substitutions = HashMap::new();
    for require in requires {
        collect_literal_equalities_from_conjunction(require, &mut substitutions);
    }
    substitutions
}

fn collect_literal_equalities_from_conjunction(
    expr: &PureExpr,
    substitutions: &mut HashMap<String, PureExpr>,
) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            collect_literal_equalities_from_conjunction(lhs, substitutions);
            collect_literal_equalities_from_conjunction(rhs, substitutions);
        }
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
            (PureExpr::Var(name, _), literal) if is_literal_substitution(literal) => {
                substitutions.insert(name.clone(), literal.clone());
            }
            (literal, PureExpr::Var(name, _)) if is_literal_substitution(literal) => {
                substitutions.insert(name.clone(), literal.clone());
            }
            _ => {}
        },
        _ => {}
    }
}

fn is_literal_substitution(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_)
    )
}

fn logic_fn_equality_orientation_has_visible_body(
    logic_call: &PureExpr,
    _expected: &PureExpr,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
) -> bool {
    let PureExpr::LogicFnCall { name, args } = logic_call else {
        return false;
    };
    logic_fns.iter().any(|logic_fn| {
        logic_fn.name() == name
            && logic_fn.params().len() == args.len()
            && logic_fn_body_visible(logic_fn)
    })
}

fn logic_fn_equality_orientation_matches_body(
    logic_call: &PureExpr,
    expected: &PureExpr,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
) -> bool {
    let PureExpr::LogicFnCall { name, args } = logic_call else {
        return false;
    };
    let Some(logic_fn) = logic_fns.iter().find(|logic_fn| {
        logic_fn.name() == name
            && logic_fn.params().len() == args.len()
            && logic_fn_body_visible(logic_fn)
            && logic_fn.requires().is_empty()
    }) else {
        return false;
    };
    let substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    // Binder-erasing (#125): formals := call arguments.
    let expanded = normalize_result_logic_body_expr(
        &logic_fn.body().substitute_binder_erasing(&substitutions),
    );
    let expected = normalize_result_logic_body_expr(expected);
    logic_body_exprs_equal(&expanded, &expected)
}

fn logic_body_exprs_equal(left: &PureExpr, right: &PureExpr) -> bool {
    if crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(left, right) {
        return true;
    }
    if let (Some(left), Some(right)) = (eval_int_literal_expr(left), eval_int_literal_expr(right)) {
        return left == right;
    }
    if let (Some(left), Some(right)) = (eval_bool_literal_expr(left), eval_bool_literal_expr(right))
    {
        return left == right;
    }
    false
}

fn eval_int_literal_expr(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if matches!(method.as_str(), "len" | "len_ghost") && args.is_empty() => {
            i64::try_from(seq_literal_elements(receiver)?.len()).ok()
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if matches!(method.as_str(), "index" | "index_logic") && args.len() == 1 => {
            let index = usize::try_from(eval_int_literal_expr(&args[0])?).ok()?;
            let elements = seq_literal_elements(receiver)?;
            elements.get(index).and_then(eval_int_literal_expr)
        }
        PureExpr::UnOp(UnOp::Neg, inner) => eval_int_literal_expr(inner)?.checked_neg(),
        PureExpr::BinOp(left, op, right) => {
            let left = eval_int_literal_expr(left)?;
            let right = eval_int_literal_expr(right)?;
            match op {
                BinOp::Add => left.checked_add(right),
                BinOp::Sub => left.checked_sub(right),
                BinOp::Mul => left.checked_mul(right),
                BinOp::Div => left.checked_div(right),
                BinOp::Mod => left.checked_rem(right),
                BinOp::DivTrunc => left.checked_div(right),
                BinOp::RemTrunc => left.checked_rem(right),
                _ => None,
            }
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            if eval_bool_literal_expr(cond)? {
                eval_int_literal_expr(then_expr)
            } else {
                eval_int_literal_expr(else_expr)
            }
        }
        // Old/Deref are same-state projections over an already-evaluated
        // value; folding them is faithful (8d7bf70's prophecy-opaque rule
        // keeps exactly these and refuses `Final`).
        PureExpr::Old(inner) | PureExpr::Deref(inner) => eval_int_literal_expr(inner),
        // ★ #125: `Final` REFUSES, mirroring 8d7bf70's
        // `refuse_prophecy_over_constant` fail-closed semantics. The old
        // RESIDUAL fold is gone: `Final(<literal>)` at this layer was
        // AMBIGUOUS between (a) the driver's borrow-chain advance of a
        // borrowed place's constant value — folding that is the `^p == *p`
        // inversion, on an ACCEPTING path
        // (`is_trivially_true_postcondition_under_requires` lets
        // `verify/pipeline.rs` mark a slice `Verified(None)` with NO SOLVE AT
        // ALL) — and (b) binder-erasing substitution of a logic-fn formal /
        // quantifier witness / match payload / `Let` value, where the fold is
        // licensed. Route (b) is now normalised AT the erasing sites
        // (`PureExpr::substitute_binder_erasing`, which rewrites
        // `^x [x := c]` to `c` before the wrapper is ever minted), so any
        // `Final` that still reaches these evaluators is either route (a) or
        // un-normalisable — refusing costs nothing legitimate and closes the
        // solver-bypassing accept. Returning `None` sends the obligation to a
        // real solve, where the encoder guard disambiguates.
        PureExpr::Final(_) => None,
        PureExpr::View(inner) => eval_int_literal_expr(inner),
        _ => None,
    }
}

fn seq_literal_elements(expr: &PureExpr) -> Option<Vec<PureExpr>> {
    match expr {
        PureExpr::LogicFnCall { name, args }
            if matches!(name.as_str(), "seq_empty" | "Seq::empty") && args.is_empty() =>
        {
            Some(Vec::new())
        }
        PureExpr::LogicFnCall { name, args }
            if matches!(name.as_str(), "seq" | "Seq::singleton") && args.len() == 1 =>
        {
            Some(vec![args[0].clone()])
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "push_back" && args.len() == 1 => {
            let mut elements = seq_literal_elements(receiver)?;
            elements.push(args[0].clone());
            Some(elements)
        }
        PureExpr::Old(inner) | PureExpr::Deref(inner) => seq_literal_elements(inner),
        // ★ #125: `Final` refuses — see `eval_int_literal_expr`.
        PureExpr::Final(_) => None,
        PureExpr::View(inner) => seq_literal_elements(inner),
        _ => None,
    }
}

fn eval_bool_literal_expr(expr: &PureExpr) -> Option<bool> {
    match expr {
        PureExpr::Bool(value) => Some(*value),
        PureExpr::UnOp(UnOp::Not, inner) => Some(!eval_bool_literal_expr(inner)?),
        PureExpr::BinOp(left, op, right) => match op {
            BinOp::And => Some(eval_bool_literal_expr(left)? && eval_bool_literal_expr(right)?),
            BinOp::Or => Some(eval_bool_literal_expr(left)? || eval_bool_literal_expr(right)?),
            BinOp::Implies => {
                Some(!eval_bool_literal_expr(left)? || eval_bool_literal_expr(right)?)
            }
            BinOp::Eq => {
                if let (Some(left), Some(right)) =
                    (eval_int_literal_expr(left), eval_int_literal_expr(right))
                {
                    return Some(left == right);
                }
                Some(eval_bool_literal_expr(left)? == eval_bool_literal_expr(right)?)
            }
            BinOp::Ne => {
                if let (Some(left), Some(right)) =
                    (eval_int_literal_expr(left), eval_int_literal_expr(right))
                {
                    return Some(left != right);
                }
                Some(eval_bool_literal_expr(left)? != eval_bool_literal_expr(right)?)
            }
            BinOp::Lt => Some(eval_int_literal_expr(left)? < eval_int_literal_expr(right)?),
            BinOp::Le => Some(eval_int_literal_expr(left)? <= eval_int_literal_expr(right)?),
            BinOp::Gt => Some(eval_int_literal_expr(left)? > eval_int_literal_expr(right)?),
            BinOp::Ge => Some(eval_int_literal_expr(left)? >= eval_int_literal_expr(right)?),
            _ => None,
        },
        PureExpr::Ite(cond, then_expr, else_expr) => {
            if eval_bool_literal_expr(cond)? {
                eval_bool_literal_expr(then_expr)
            } else {
                eval_bool_literal_expr(else_expr)
            }
        }
        PureExpr::Old(inner) | PureExpr::Deref(inner) => eval_bool_literal_expr(inner),
        // ★ #125: `Final` refuses — see `eval_int_literal_expr`.
        PureExpr::Final(_) => None,
        PureExpr::View(inner) => eval_bool_literal_expr(inner),
        _ => None,
    }
}

fn inline_result_logic_body_equality(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> Option<PureExpr> {
    let logic_fns = logic_fns?;
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = ensure else {
        return None;
    };

    let (result_side, logic_call) = match (lhs.as_ref(), rhs.as_ref()) {
        (PureExpr::Var(name, _), call) if name == "result" => (lhs.as_ref().clone(), call),
        (call, PureExpr::Var(name, _)) if name == "result" => (rhs.as_ref().clone(), call),
        _ => return None,
    };
    let PureExpr::LogicFnCall { name, args } = logic_call else {
        return None;
    };

    let logic_fn = logic_fns
        .iter()
        .find(|f| f.name() == name && f.params().len() == args.len() && logic_fn_body_visible(f))?;
    if !logic_fn.requires().is_empty() {
        return None;
    }

    let substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    // Binder-erasing (#125): formals := call arguments.
    let expanded = normalize_result_logic_body_expr(
        &logic_fn.body().substitute_binder_erasing(&substitutions),
    );
    Some(PureExpr::BinOp(
        Arc::new(result_side),
        BinOp::Eq,
        Arc::new(expanded),
    ))
}

fn normalize_result_logic_body_expr(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Var(name, _) if name == "USIZE_BITS" => {
            PureExpr::Int((std::mem::size_of::<usize>() * 8) as i64)
        }
        PureExpr::Let { var, value, body } => {
            let mut substitutions = HashMap::new();
            substitutions.insert(var.clone(), normalize_result_logic_body_expr(value));
            // Binder-erasing (#125): `Let` var := value.
            normalize_result_logic_body_expr(&body.substitute_binder_erasing(&substitutions))
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(normalize_result_logic_body_expr(left)),
            *op,
            Arc::new(normalize_result_logic_body_expr(right)),
        ),
        PureExpr::UnOp(op, inner) => {
            PureExpr::UnOp(*op, Arc::new(normalize_result_logic_body_expr(inner)))
        }
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(normalize_result_logic_body_expr(cond)),
            Arc::new(normalize_result_logic_body_expr(then_expr)),
            Arc::new(normalize_result_logic_body_expr(else_expr)),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(normalize_result_logic_body_expr(inner))),
        // Strip `Deref` (the `*expr` form, encoding the current value of a
        // borrow) symmetrically — same justification as `View` and
        // `deep_model`: `Deref` is a deterministic projection, so if both
        // sides of an equality cancel through `*`, the stripped operands being
        // syntactically equal implies the original equality holds by
        // congruence of `Deref` over `=`. (Phase 3 B4)
        PureExpr::Deref(inner) => normalize_result_logic_body_expr(inner),
        PureExpr::Final(inner) => {
            PureExpr::Final(Arc::new(normalize_result_logic_body_expr(inner)))
        }
        PureExpr::View(inner) => normalize_result_logic_body_expr(inner),
        // Treat the explicit method-call form `expr.view()` identically to
        // the `View(expr)` operator (parsed from `expr@`). Both lower to
        // `encode_view_expr` in the encoder, so the body matcher must strip
        // them on both sides to keep the comparison symmetric. (Phase 3 B4)
        //
        // `expr.deep_model()` is stripped on the same structural-cancellation
        // grounds: it is a deterministic function of its receiver, so if both
        // sides of the equality use `.deep_model()` then `strip(LHS) ==
        // strip(RHS)` (as Rust-level values) implies the original logical
        // equality by congruence. (Phase 3 B4)
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if (method == "view" || method == "deep_model") && args.is_empty() => {
            normalize_result_logic_body_expr(receiver)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(normalize_result_logic_body_expr(receiver)),
            method: method.clone(),
            args: args.iter().map(normalize_result_logic_body_expr).collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args.iter().map(normalize_result_logic_body_expr).collect(),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(normalize_result_logic_body_expr(assumption)),
            body: Arc::new(normalize_result_logic_body_expr(body)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(normalize_result_logic_body_expr(obligation)),
            body: Arc::new(normalize_result_logic_body_expr(body)),
        },
        _ => expr.clone(),
    }
}

fn simplify_logic_body_expr_under_requires(expr: &PureExpr, requires: &[PureExpr]) -> PureExpr {
    let substitutions = substitutions_from_requires(requires);
    let expr = substitute_until_stable(expr, &substitutions);
    simplify_logic_body_expr_under_requires_inner(&expr, requires)
}

fn substitute_until_stable(expr: &PureExpr, substitutions: &HashMap<String, PureExpr>) -> PureExpr {
    if substitutions.is_empty() {
        return expr.clone();
    }

    let mut current = expr.clone();
    for _ in 0..8 {
        let next = current.substitute(substitutions);
        if next == current {
            return next;
        }
        current = next;
    }
    current
}

fn substitutions_from_requires(requires: &[PureExpr]) -> HashMap<String, PureExpr> {
    let mut substitutions = HashMap::new();
    for require in requires {
        collect_substitutions_from_require(require, &mut substitutions);
    }
    substitutions
}

fn collect_substitutions_from_require(
    require: &PureExpr,
    substitutions: &mut HashMap<String, PureExpr>,
) {
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_substitutions_from_require(left, substitutions);
            collect_substitutions_from_require(right, substitutions);
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            collect_var_literal_substitution(left, right, substitutions);
            collect_var_literal_substitution(right, left, substitutions);
        }
        _ => {}
    }
}

fn collect_var_literal_substitution(
    var: &PureExpr,
    value: &PureExpr,
    substitutions: &mut HashMap<String, PureExpr>,
) {
    let PureExpr::Var(name, _) = var else {
        return;
    };
    let Some(literal) = literal_substitution_value(value) else {
        return;
    };
    substitutions.entry(name.clone()).or_insert(literal);
}

fn literal_substitution_value(value: &PureExpr) -> Option<PureExpr> {
    match value {
        PureExpr::Int(_) | PureExpr::Bool(_) => Some(value.clone()),
        PureExpr::LogicFnCall { name, args }
            if matches!(name.as_str(), "seq_empty" | "Seq::empty") && args.is_empty() =>
        {
            Some(value.clone())
        }
        PureExpr::LogicFnCall { name, args }
            if matches!(name.as_str(), "seq" | "Seq::singleton") && args.len() == 1 =>
        {
            Some(value.clone())
        }
        PureExpr::MethodCall { method, .. } if method == "push_back" => {
            seq_literal_elements(value)?;
            Some(value.clone())
        }
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            literal_substitution_value(inner)
        }
        PureExpr::View(inner) => literal_substitution_value(inner),
        _ => None,
    }
}

/// BV-absorption rewrites for set-bit / unset-bit shaped obligations (#5).
///
/// Returns the absorbed expression when the AND collapses by a BV identity:
/// - `(A | M) & M = M`   (set-bit: `(bitvec | (1<<bit)) & (1<<bit)`)
/// - `M & (A | M) = M`
/// - `(A & ~M) & M = 0`  (unset-bit: `(bitvec & !(1<<bit)) & (1<<bit)`)
/// - `M & (A & ~M) = 0`
///
/// Looks through `LetAssume`/`LetObligation` wrappers because the driver
/// wraps return-expression bodies in let-assumes capturing precondition
/// facts (e.g., `let_assume(bit < 64) { bitvec | (1 << bit) }`).
/// Sort-agnostic equality (#2673) is used because the driver may attach
/// different `ExprSort` annotations to syntactically identical operands.
fn bitand_or_absorption(left: &PureExpr, right: &PureExpr) -> Option<PureExpr> {
    let eq = crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal;
    let left_body = let_wrapper_body(left);
    let right_body = let_wrapper_body(right);
    // `(A | M) & M = M`
    if let PureExpr::BinOp(or_left, BinOp::BitOr, or_right) = left_body {
        if eq(or_left, right_body) || eq(or_right, right_body) {
            return Some(right.clone());
        }
    }
    if let PureExpr::BinOp(or_left, BinOp::BitOr, or_right) = right_body {
        if eq(or_left, left_body) || eq(or_right, left_body) {
            return Some(left.clone());
        }
    }
    // `(A & ~M) & M = 0` — when one operand contains `& ~M` whose `M`
    // matches the other operand. Used by `unset_bit` whose body is
    // `bitvec & !(1<<bit)`.
    if bitand_complement_yields_zero(left_body, right_body)
        || bitand_complement_yields_zero(right_body, left_body)
    {
        return Some(PureExpr::Int(0));
    }
    None
}

/// Return true when `left_body` contains a BV `BitAnd` with one operand
/// equal to `~mask`, where `mask` matches `right_body`.
fn bitand_complement_yields_zero(left_body: &PureExpr, right_body: &PureExpr) -> bool {
    let eq = crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal;
    let PureExpr::BinOp(and_left, BinOp::BitAnd, and_right) = left_body else {
        return false;
    };
    let is_complement_of_mask = |operand: &PureExpr| -> bool {
        let PureExpr::UnOp(op, inner) = operand else {
            return false;
        };
        if !matches!(op, UnOp::BitNot | UnOp::Not) {
            return false;
        }
        eq(inner, right_body)
    };
    is_complement_of_mask(and_left) || is_complement_of_mask(and_right)
}

/// Strip `LetAssume`/`LetObligation` wrappers used to carry precondition
/// facts into a body, returning the inner body for structural matching.
fn let_wrapper_body(expr: &PureExpr) -> &PureExpr {
    let mut current = expr;
    loop {
        match current {
            PureExpr::LetAssume { body, .. } | PureExpr::LetObligation { body, .. } => {
                current = body;
            }
            _ => return current,
        }
    }
}

fn simplify_logic_body_expr_under_requires_inner(
    expr: &PureExpr,
    requires: &[PureExpr],
) -> PureExpr {
    match expr {
        PureExpr::BinOp(left, op, right) => {
            let left = simplify_logic_body_expr_under_requires_inner(left, requires);
            let right = simplify_logic_body_expr_under_requires_inner(right, requires);
            // BV absorption (#5): `(A | M) & M = M` and `M & (A | M) = M`.
            // The set-bit postcondition `has_bit(result, bit)` inlines to
            // `(bitvec | (1<<bit)) & (1<<bit) != 0`; reducing the AND to its
            // absorbed RHS lets the resulting `(1<<bit) != 0` be discharged
            // via the shift-in-range trivially-true check below.
            if matches!(op, BinOp::BitAnd) {
                if let Some(absorbed) = bitand_or_absorption(&left, &right) {
                    return absorbed;
                }
            }
            PureExpr::BinOp(Arc::new(left), *op, Arc::new(right))
        }
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(simplify_logic_body_expr_under_requires_inner(
                inner, requires,
            )),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let cond = simplify_logic_body_expr_under_requires_inner(cond, requires);
            if requires_imply_expr(&cond, requires) {
                return simplify_logic_body_expr_under_requires_inner(then_expr, requires);
            }
            if requires_imply_expr_false(&cond, requires) {
                return simplify_logic_body_expr_under_requires_inner(else_expr, requires);
            }
            PureExpr::Ite(
                Arc::new(cond),
                Arc::new(simplify_logic_body_expr_under_requires_inner(
                    then_expr, requires,
                )),
                Arc::new(simplify_logic_body_expr_under_requires_inner(
                    else_expr, requires,
                )),
            )
        }
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(
            simplify_logic_body_expr_under_requires_inner(inner, requires),
        )),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(
            simplify_logic_body_expr_under_requires_inner(inner, requires),
        )),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(
            simplify_logic_body_expr_under_requires_inner(inner, requires),
        )),
        PureExpr::View(inner) => PureExpr::View(Arc::new(
            simplify_logic_body_expr_under_requires_inner(inner, requires),
        )),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(simplify_logic_body_expr_under_requires_inner(
                receiver, requires,
            )),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| simplify_logic_body_expr_under_requires_inner(arg, requires))
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| simplify_logic_body_expr_under_requires_inner(arg, requires))
                .collect(),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(simplify_logic_body_expr_under_requires_inner(
                assumption, requires,
            )),
            body: Arc::new(simplify_logic_body_expr_under_requires_inner(
                body, requires,
            )),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(simplify_logic_body_expr_under_requires_inner(
                obligation, requires,
            )),
            body: Arc::new(simplify_logic_body_expr_under_requires_inner(
                body, requires,
            )),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(simplify_logic_body_expr_under_requires_inner(
                body, requires,
            )),
            triggers: triggers.clone(),
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Exists {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(simplify_logic_body_expr_under_requires_inner(
                body, requires,
            )),
            triggers: triggers.clone(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(simplify_logic_body_expr_under_requires_inner(
                scrutinee, requires,
            )),
            arms: arms
                .iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: simplify_logic_body_expr_under_requires_inner(&arm.body, requires),
                })
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(simplify_logic_body_expr_under_requires_inner(
                value, requires,
            )),
            body: Arc::new(simplify_logic_body_expr_under_requires_inner(
                body, requires,
            )),
        },
        other => other.clone(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum IntRel {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
}

impl IntRel {
    fn negate(self) -> Option<Self> {
        match self {
            Self::Lt => Some(Self::Ge),
            Self::Le => Some(Self::Gt),
            Self::Gt => Some(Self::Le),
            Self::Ge => Some(Self::Lt),
            Self::Eq => None,
        }
    }
}

fn requires_imply_expr(expr: &PureExpr, requires: &[PureExpr]) -> bool {
    if matches!(expr, PureExpr::Bool(true)) {
        return true;
    }
    if matches!(expr, PureExpr::Bool(false)) {
        return false;
    }
    requires
        .iter()
        .any(|require| require_implies_expr(require, expr))
}

fn requires_imply_expr_false(expr: &PureExpr, requires: &[PureExpr]) -> bool {
    if matches!(expr, PureExpr::Bool(false)) {
        return true;
    }
    if matches!(expr, PureExpr::Bool(true)) {
        return false;
    }
    requires
        .iter()
        .any(|require| require_implies_expr_false(require, expr))
}

fn require_implies_expr(require: &PureExpr, expr: &PureExpr) -> bool {
    if crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(require, expr) {
        return true;
    }
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            require_implies_expr(left, expr) || require_implies_expr(right, expr)
        }
        _ => compare_int_bound_implication(require, expr),
    }
}

fn require_implies_expr_false(require: &PureExpr, expr: &PureExpr) -> bool {
    if let PureExpr::UnOp(UnOp::Not, inner) = require {
        if crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(inner, expr) {
            return true;
        }
    }
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            require_implies_expr_false(left, expr) || require_implies_expr_false(right, expr)
        }
        _ => compare_int_bound_implication_to_negation(require, expr),
    }
}

fn compare_int_bound_implication(require: &PureExpr, expr: &PureExpr) -> bool {
    let Some((req_value, req_rel, req_const)) = int_bound(require) else {
        return false;
    };
    let Some((expr_value, expr_rel, expr_const)) = int_bound(expr) else {
        return false;
    };
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(req_value, expr_value)
        && int_rel_implies(req_rel, req_const, expr_rel, expr_const)
}

fn compare_int_bound_implication_to_negation(require: &PureExpr, expr: &PureExpr) -> bool {
    let Some((req_value, req_rel, req_const)) = int_bound(require) else {
        return false;
    };
    let Some((expr_value, expr_rel, expr_const)) = int_bound(expr) else {
        return false;
    };
    let Some(negated_expr_rel) = expr_rel.negate() else {
        return false;
    };
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(req_value, expr_value)
        && int_rel_implies(req_rel, req_const, negated_expr_rel, expr_const)
}

fn int_bound(expr: &PureExpr) -> Option<(&PureExpr, IntRel, i64)> {
    let PureExpr::BinOp(left, op, right) = expr else {
        return None;
    };
    // `View(Int(n))` evaluates to `n` because the driver's integer view
    // is the identity on `Int` (#5). Stripping View on the literal side
    // lets us match `View(bit) < View(64)` against an `Int(64)` goal.
    let left_lit = int_literal_through_view(left.as_ref());
    let right_lit = int_literal_through_view(right.as_ref());
    match (left_lit, op, right_lit) {
        (None, BinOp::Lt, Some(n)) => Some((left.as_ref(), IntRel::Lt, n)),
        (None, BinOp::Le, Some(n)) => Some((left.as_ref(), IntRel::Le, n)),
        (None, BinOp::Gt, Some(n)) => Some((left.as_ref(), IntRel::Gt, n)),
        (None, BinOp::Ge, Some(n)) => Some((left.as_ref(), IntRel::Ge, n)),
        (None, BinOp::Eq, Some(n)) => Some((left.as_ref(), IntRel::Eq, n)),
        (Some(n), BinOp::Lt, None) => Some((right.as_ref(), IntRel::Gt, n)),
        (Some(n), BinOp::Le, None) => Some((right.as_ref(), IntRel::Ge, n)),
        (Some(n), BinOp::Gt, None) => Some((right.as_ref(), IntRel::Lt, n)),
        (Some(n), BinOp::Ge, None) => Some((right.as_ref(), IntRel::Le, n)),
        (Some(n), BinOp::Eq, None) => Some((right.as_ref(), IntRel::Eq, n)),
        _ => None,
    }
}

/// `View(Int(n))` evaluates to the same integer literal `n` because the
/// driver's integer view is the identity on `Int` (the driver inserts
/// `View(...)` wrappers around integer-typed arguments uniformly). Strip
/// one `View` wrapper so int-bound implications discharge `View(bit) <
/// View(64)` against an `Int(64)`-formed goal. (#5)
fn int_literal_through_view(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::Int(n) => Some(*n),
        PureExpr::View(inner) => int_literal_through_view(inner),
        _ => None,
    }
}

fn int_rel_implies(req_rel: IntRel, req_const: i64, goal_rel: IntRel, goal_const: i64) -> bool {
    match req_rel {
        IntRel::Eq => match goal_rel {
            IntRel::Eq => req_const == goal_const,
            IntRel::Lt => req_const < goal_const,
            IntRel::Le => req_const <= goal_const,
            IntRel::Gt => req_const > goal_const,
            IntRel::Ge => req_const >= goal_const,
        },
        IntRel::Gt => match goal_rel {
            IntRel::Gt => req_const >= goal_const,
            IntRel::Ge => req_const >= goal_const.saturating_sub(1),
            _ => false,
        },
        IntRel::Ge => match goal_rel {
            IntRel::Gt => req_const > goal_const,
            IntRel::Ge => req_const >= goal_const,
            _ => false,
        },
        IntRel::Lt => match goal_rel {
            IntRel::Lt => req_const <= goal_const,
            IntRel::Le => req_const <= goal_const.saturating_add(1),
            _ => false,
        },
        IntRel::Le => match goal_rel {
            IntRel::Lt => req_const < goal_const,
            IntRel::Le => req_const <= goal_const,
            _ => false,
        },
    }
}

fn requirements_imply_normalized_expr(expr: &PureExpr, requires: &[PureExpr]) -> bool {
    match expr {
        PureExpr::Bool(true) => true,
        PureExpr::Bool(false) => false,
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirements_imply_normalized_expr(left, requires)
                && requirements_imply_normalized_expr(right, requires)
        }
        _ => requires
            .iter()
            .any(|require| require_implies_expr(require, expr)),
    }
}

const MAX_LOGIC_FN_INLINE_DEPTH: usize = 32;

fn inline_logic_fn_calls_from_defs(
    expr: &PureExpr,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
) -> PureExpr {
    inline_logic_fn_calls_from_defs_under_requires(expr, logic_fns, &[])
}

fn inline_logic_fn_calls_from_defs_under_requires(
    expr: &PureExpr,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
    requires: &[PureExpr],
) -> PureExpr {
    inline_logic_fn_calls_from_defs_with_depth(expr, logic_fns, requires, 0)
}

fn inline_logic_fn_calls_from_defs_with_depth(
    expr: &PureExpr,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
    requires: &[PureExpr],
    depth: usize,
) -> PureExpr {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            let expanded_args: Vec<PureExpr> = args
                .iter()
                .map(|arg| {
                    inline_logic_fn_calls_from_defs_with_depth(arg, logic_fns, requires, depth)
                })
                .collect();
            if depth >= MAX_LOGIC_FN_INLINE_DEPTH {
                return PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: expanded_args,
                };
            }
            let Some(logic_fn) = logic_fns.iter().find(|logic_fn| {
                logic_fn.name() == name
                    && logic_fn.params().len() == expanded_args.len()
                    && logic_fn_body_available_under_requires(logic_fn, &expanded_args, requires)
            }) else {
                return PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: expanded_args,
                };
            };
            let substitutions: HashMap<String, PureExpr> = logic_fn
                .params()
                .iter()
                .cloned()
                .zip(expanded_args)
                .collect();
            // Binder-erasing (#125): formals := call arguments.
            let expanded = logic_fn.body().substitute_binder_erasing(&substitutions);
            inline_logic_fn_calls_from_defs_with_depth(&expanded, logic_fns, requires, depth + 1)
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                left, logic_fns, requires, depth,
            )),
            *op,
            Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                right, logic_fns, requires, depth,
            )),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                inner, logic_fns, requires, depth,
            )),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                cond, logic_fns, requires, depth,
            )),
            Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                then_expr, logic_fns, requires, depth,
            )),
            Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                else_expr, logic_fns, requires, depth,
            )),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(
            inline_logic_fn_calls_from_defs_with_depth(inner, logic_fns, requires, depth),
        )),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(
            inline_logic_fn_calls_from_defs_with_depth(inner, logic_fns, requires, depth),
        )),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(
            inline_logic_fn_calls_from_defs_with_depth(inner, logic_fns, requires, depth),
        )),
        PureExpr::View(inner) => PureExpr::View(Arc::new(
            inline_logic_fn_calls_from_defs_with_depth(inner, logic_fns, requires, depth),
        )),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let expanded_receiver =
                inline_logic_fn_calls_from_defs_with_depth(receiver, logic_fns, requires, depth);
            let expanded_args: Vec<PureExpr> = args
                .iter()
                .map(|arg| {
                    inline_logic_fn_calls_from_defs_with_depth(arg, logic_fns, requires, depth)
                })
                .collect();
            let mut logic_args = Vec::with_capacity(expanded_args.len() + 1);
            logic_args.push(expanded_receiver.clone());
            logic_args.extend(expanded_args.iter().cloned());
            if depth < MAX_LOGIC_FN_INLINE_DEPTH {
                if let Some(logic_fn) = logic_fns.iter().find(|logic_fn| {
                    logic_fn.name() == method
                        && logic_fn.params().len() == logic_args.len()
                        && logic_fn_body_available_under_requires(logic_fn, &logic_args, requires)
                }) {
                    let substitutions: HashMap<String, PureExpr> =
                        logic_fn.params().iter().cloned().zip(logic_args).collect();
                    // Binder-erasing (#125): formals := call arguments.
                    let expanded = logic_fn.body().substitute_binder_erasing(&substitutions);
                    return inline_logic_fn_calls_from_defs_with_depth(
                        &expanded,
                        logic_fns,
                        requires,
                        depth + 1,
                    );
                }
            }
            PureExpr::MethodCall {
                receiver: Arc::new(expanded_receiver),
                method: method.clone(),
                args: expanded_args,
            }
        }
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                assumption, logic_fns, requires, depth,
            )),
            body: Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                body, logic_fns, requires, depth,
            )),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                obligation, logic_fns, requires, depth,
            )),
            body: Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                body, logic_fns, requires, depth,
            )),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                body, logic_fns, requires, depth,
            )),
            triggers: triggers.clone(),
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Exists {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                body, logic_fns, requires, depth,
            )),
            triggers: triggers.clone(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                scrutinee, logic_fns, requires, depth,
            )),
            arms: arms
                .iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: inline_logic_fn_calls_from_defs_with_depth(
                        &arm.body, logic_fns, requires, depth,
                    ),
                })
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                value, logic_fns, requires, depth,
            )),
            body: Arc::new(inline_logic_fn_calls_from_defs_with_depth(
                body, logic_fns, requires, depth,
            )),
        },
        other => other.clone(),
    }
}

fn normalize_entailment_expr(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::UnOp(UnOp::Not, inner) => normalize_negated_entailment_expr(inner),
        PureExpr::BinOp(left, BinOp::And, right) => {
            let left = normalize_entailment_expr(left);
            let right = normalize_entailment_expr(right);
            match (&left, &right) {
                (PureExpr::Bool(false), _) | (_, PureExpr::Bool(false)) => PureExpr::Bool(false),
                (PureExpr::Bool(true), _) => right,
                (_, PureExpr::Bool(true)) => left,
                _ => PureExpr::BinOp(Arc::new(left), BinOp::And, Arc::new(right)),
            }
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(normalize_entailment_expr(left)),
            *op,
            Arc::new(normalize_entailment_expr(right)),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(normalize_entailment_expr(cond)),
            Arc::new(normalize_entailment_expr(then_expr)),
            Arc::new(normalize_entailment_expr(else_expr)),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(normalize_entailment_expr(inner))),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(normalize_entailment_expr(inner))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(normalize_entailment_expr(inner))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(normalize_entailment_expr(inner))),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(normalize_entailment_expr(receiver)),
            method: method.clone(),
            args: args.iter().map(normalize_entailment_expr).collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args.iter().map(normalize_entailment_expr).collect(),
        },
        other => other.clone(),
    }
}

fn normalize_negated_entailment_expr(expr: &PureExpr) -> PureExpr {
    match normalize_entailment_expr(expr) {
        PureExpr::Bool(value) => PureExpr::Bool(!value),
        PureExpr::UnOp(UnOp::Not, inner) => inner.as_ref().clone(),
        PureExpr::BinOp(left, BinOp::Lt, right) => PureExpr::BinOp(left, BinOp::Ge, right),
        PureExpr::BinOp(left, BinOp::Le, right) => PureExpr::BinOp(left, BinOp::Gt, right),
        PureExpr::BinOp(left, BinOp::Gt, right) => PureExpr::BinOp(left, BinOp::Le, right),
        PureExpr::BinOp(left, BinOp::Ge, right) => PureExpr::BinOp(left, BinOp::Lt, right),
        other => PureExpr::UnOp(UnOp::Not, Arc::new(other)),
    }
}

/// Check if an expression is a triggerless universal quantifier.
///
/// Returns `true` for `forall<v> body` with no triggers, including
/// nested triggerless foralls like `forall<a> forall<b> body`.
/// Returns `false` for non-universal expressions or universals with
/// user-provided triggers.
///
/// Used to route all-universal postcondition sets to the slow path
/// for Skolemization when ay-dpll lacks E-matching triggers. (#1296)
fn is_triggerless_universal(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Forall { body, triggers, .. } => {
            // Has user-provided triggers — ay's native handling may work.
            if !triggers.is_empty() {
                return false;
            }
            // Check nested foralls: all must be triggerless.
            match body.as_ref() {
                PureExpr::Forall { .. } => is_triggerless_universal(body),
                _ => true,
            }
        }
        _ => false,
    }
}

fn collect_top_level_conjuncts<'a>(expr: &'a PureExpr, conjuncts: &mut Vec<&'a PureExpr>) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            collect_top_level_conjuncts(lhs, conjuncts);
            collect_top_level_conjuncts(rhs, conjuncts);
        }
        _ => conjuncts.push(expr),
    }
}

/// Route selected for negated postcondition encoding.
///
/// This is a shared classification hook for mixed and triggerless universal
/// postconditions. It captures the reusable decision point that determines
/// whether we can stay on the fast Bool-negation path or must drop to the
/// slow per-clause path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NegatedPostconditionRoute {
    Fast,
    SlowEmbeddedExistential,
    SlowMixedUniversal,
    SlowTriggerlessUniversal,
}

impl std::fmt::Display for NegatedPostconditionRoute {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let label = match self {
            Self::Fast => "fast",
            Self::SlowEmbeddedExistential => "slow:embedded-existential",
            Self::SlowMixedUniversal => "slow:mixed-universal",
            Self::SlowTriggerlessUniversal => "slow:triggerless-universal",
        };
        f.write_str(label)
    }
}

/// Classify the negated-postcondition encoding route for a set of ensures.
///
/// This is the central reusable hook for mixed universal/non-universal and
/// triggerless universal postconditions. The encoder and tests use the same
/// decision, so introspection and behavior stay aligned.
pub(crate) fn classify_negated_postcondition_route(
    ensures: &[PureExpr],
) -> NegatedPostconditionRoute {
    let has_existential = ensures
        .iter()
        .any(|e| matches!(e, PureExpr::Exists { .. }) || expr_contains_embedded_existential(e));
    let has_universal = ensures
        .iter()
        .any(|e| matches!(e, PureExpr::Forall { .. }) || expr_contains_embedded_universal(e));
    let has_non_universal = ensures
        .iter()
        .any(|e| !matches!(e, PureExpr::Forall { .. }));
    let mixed_universal = has_universal && has_non_universal;
    let all_universal_triggerless =
        has_universal && !has_non_universal && ensures.iter().all(|e| is_triggerless_universal(e));

    if mixed_universal {
        NegatedPostconditionRoute::SlowMixedUniversal
    } else if all_universal_triggerless {
        NegatedPostconditionRoute::SlowTriggerlessUniversal
    } else if has_existential {
        NegatedPostconditionRoute::SlowEmbeddedExistential
    } else {
        NegatedPostconditionRoute::Fast
    }
}

/// Encode a single postcondition and return its negation term.
///
/// Shared between the function and mut-borrow verification paths so new
/// postcondition-negation strategies land once. (#2365)
///
/// Skolemization of triggerless universals is now unconditional in the slow
/// path (the previous `force_skolemize` gate was removed; see the
/// Skolemization branch below). (#2696)
pub(crate) fn encode_negated_postcondition(
    encoder: &mut AYEncoder,
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    return_expr: Option<&PureExpr>,
) -> Result<Term, EncodingError> {
    // Trivially-true postcondition short-circuit (#2696, #2673): if the ensures
    // clause is statically known to be true (reflexive equality like
    // `u(*a) == u(*a)`, Bool(true), or quantifier with trivially-true body),
    // return `false` directly (NOT true = false). This avoids encoding
    // logic function calls that produce quantified axioms leading to
    // quantifier-unhandled results (bug/206). Uses sort-agnostic comparison
    // for reflexive equality since the driver may attach different ExprSort
    // annotations to syntactically identical expressions.
    if is_trivially_true_postcondition(ensure) {
        return Ok(encoder.solver_mut().bool_const(false));
    }
    if result_postcondition_matches_return_expr(ensure, return_expr, &[]) {
        return Ok(encoder.solver_mut().bool_const(false));
    }
    if super::function::result_binding::result_match_postcondition_directly_valid(
        ensure,
        return_expr,
    ) {
        return Ok(encoder.solver_mut().bool_const(false));
    }
    if postcondition_true_via_logic_bodies(ensure, logic_fns) {
        return Ok(encoder.solver_mut().bool_const(false));
    }
    if result_equals_return_expr_via_logic_body(ensure, logic_fns, return_expr) {
        return Ok(encoder.solver_mut().bool_const(false));
    }
    if let Some(inlined) = inline_result_logic_body_equality(ensure, logic_fns) {
        if is_trivially_true_postcondition(&inlined)
            || result_equals_return_expr_via_logic_body(&inlined, logic_fns, return_expr)
        {
            return Ok(encoder.solver_mut().bool_const(false));
        }
        let term = encoder.encode_formula(&inlined)?;
        let term = encoder.coerce_bool_operand(term);
        return Ok(encoder.solver_mut().not(term));
    }
    if let Some(term) =
        encode_negated_selected_result_match_arm(encoder, ensure, logic_fns, return_expr)?
    {
        return Ok(term);
    }
    if let Some(term) = encode_negated_result_match_over_option_ite(encoder, ensure, return_expr)? {
        return Ok(term);
    }

    // Top-level implication postconditions are common in driver contracts:
    // `guard ==> post`. Negating them as a ay-level `not(implies(...))` leaves
    // the solver to expose the propositional shape itself. Encode the
    // equivalent `guard && !post` directly so each side is dispatched in Bool
    // formula context and the SAT query starts from the simpler obligation.
    if let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = ensure {
        let mut antecedent_conjuncts = Vec::new();
        collect_top_level_conjuncts(antecedent, &mut antecedent_conjuncts);
        let mut terms = Vec::with_capacity(antecedent_conjuncts.len() + 1);
        for conjunct in antecedent_conjuncts {
            let term = encoder.encode_formula(conjunct)?;
            terms.push(encoder.coerce_bool_operand(term));
        }
        let consequent = encoder.encode_formula(consequent)?;
        let consequent = encoder.coerce_bool_operand(consequent);
        terms.push(encoder.solver_mut().not(consequent));
        return Ok(if terms.len() == 1 {
            terms
                .into_iter()
                .next()
                .expect("negated consequent always present")
        } else {
            encoder.solver_mut().and_many(&terms)
        });
    }

    if let Some(ground_instance) =
        encode_ground_negated_existential_instance(encoder, ensure, return_expr)?
    {
        return Ok(ground_instance);
    }
    if instantiate_top_level_existential_with_trivial_witness(ensure).is_some() {
        return Ok(encoder.solver_mut().bool_const(false));
    }

    if let Some(negated_expr) = negate_existential_postcondition(ensure) {
        let rewritten_neg = encoder.encode_pure(&negated_expr)?;
        if top_level_existential_body(ensure)
            .is_some_and(|(_, body)| AYEncoder::body_has_any_postcondition_mut(body))
        {
            return Ok(rewritten_neg);
        }
        // Encode the original postcondition in Bool formula context so that
        // predicate lookups (Mapping index_logic, etc.) produce Bool-sorted
        // terms directly instead of Int-sorted values that crash `not`. (#2245)
        let original = encoder.encode_formula(ensure)?;
        let original = encoder.coerce_bool_operand(original);
        let direct_neg = encoder.solver_mut().not(original);
        let false_const = encoder.solver_mut().bool_const(false);
        if direct_neg == false_const {
            return Ok(false_const);
        }
        Ok(encoder.solver_mut().or(rewritten_neg, direct_neg))
    } else if let Some(skolemized_neg) = skolemize_negated_universal(ensure) {
        // Skolemize top-level universal postconditions at the PureExpr level.
        // ay-dpll's NOT(forall ...) handling is weak — it cannot instantiate
        // the negated universal effectively. PureExpr-level Skolemization
        // creates ground Skolem constants that are visible to the encoder's
        // ground pool and trigger E-matching on defining axioms. (#1296, #2696)
        //
        // Unconditional in the slow path: previously gated on has_open_logic_fns(),
        // but that caused quantifier-unhandled on mixed universal/non-universal
        // postconditions without open logic fns (e.g., vector/09_capacity.rs). (#2696)
        //
        // If Skolemized encoding fails (e.g., the body references unregistered
        // method calls that `encode_pure` cannot resolve), fall back to the
        // ay-level NOT path which uses `encode_formula` instead. (#1296)
        match encoder.encode_pure(&skolemized_neg) {
            Ok(term) => {
                // Emit placeholder-constructor bridge facts for nested-payload
                // guards in the skolemized postcondition (e.g.
                // result/own.rs::transpose's `self = Ok(Some(sk_t))`), which the
                // stack-scanning ground-consequence pass does not reach on this
                // solve path. (#transpose)
                encoder.emit_placeholder_bridge_facts_from_term(term);
                Ok(term)
            }
            Err(_) => {
                // Skolemization encoding failed — fall back to ay-level NOT.
                let term = encoder.encode_formula(ensure)?;
                let term = encoder.coerce_bool_operand(term);
                Ok(encoder.solver_mut().not(term))
            }
        }
    } else if has_open_logic_fns(logic_fns) {
        // Non-universal with open logic fns: standard ay-level NOT.
        let term = encoder.encode_formula(ensure)?;
        let term = encoder.coerce_bool_operand(term);
        Ok(encoder.solver_mut().not(term))
    } else if expr_contains_embedded_existential(ensure) {
        let instantiated = instantiate_embedded_existentials_with_body_witness(ensure, return_expr);
        // Bool formula context for the witness-instantiated form. (#2245)
        let term = encoder.encode_formula(&instantiated)?;
        let term = encoder.coerce_bool_operand(term);
        Ok(encoder.solver_mut().not(term))
    } else {
        // Bool formula context: predicate lookups produce Bool. (#2245)
        let term = encoder.encode_formula(ensure)?;
        let term = encoder.coerce_bool_operand(term);
        Ok(encoder.solver_mut().not(term))
    }
}

fn encode_negated_selected_result_match_arm(
    encoder: &mut AYEncoder,
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    return_expr: Option<&PureExpr>,
) -> Result<Option<Term>, EncodingError> {
    let PureExpr::Match { scrutinee, arms } = ensure else {
        return Ok(None);
    };
    if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result") {
        return Ok(None);
    }
    let Some(return_expr) = return_expr.map(strip_let_assume) else {
        return Ok(None);
    };
    encode_negated_selected_result_match_arm_for_value(encoder, arms, return_expr, logic_fns, false)
}

fn selected_result_match_arm_body_for_return(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> Option<PureExpr> {
    let PureExpr::Match { scrutinee, arms } = ensure else {
        return None;
    };
    if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result") {
        return None;
    }
    let return_expr = return_expr.map(strip_let_assume)?;
    selected_option_bool_match_arm_body(arms, return_expr)
        .or_else(|| selected_match_arm_body_for_expr(arms, return_expr))
}

fn encode_negated_selected_result_match_arm_for_value(
    encoder: &mut AYEncoder,
    arms: &[trust_wp_core::formula::MatchArm],
    value: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    allow_fallback_match: bool,
) -> Result<Option<Term>, EncodingError> {
    let value = strip_let_assume(value);
    if let Some(selected_body) = selected_option_bool_match_arm_body(arms, value) {
        return encode_negated_postcondition(encoder, &selected_body, logic_fns, None).map(Some);
    }
    if let Some(selected_body) = selected_match_arm_body_for_expr(arms, value) {
        return encode_negated_postcondition(encoder, &selected_body, logic_fns, None).map(Some);
    }

    let PureExpr::Ite(condition, then_branch, else_branch) = value else {
        if allow_fallback_match {
            return encode_negated_match_with_scrutinee(encoder, arms, value, logic_fns).map(Some);
        }
        return Ok(None);
    };
    let Some(then_negated) = encode_negated_selected_result_match_arm_for_value(
        encoder,
        arms,
        then_branch,
        logic_fns,
        true,
    )?
    else {
        return Ok(None);
    };
    let Some(else_negated) = encode_negated_selected_result_match_arm_for_value(
        encoder,
        arms,
        else_branch,
        logic_fns,
        true,
    )?
    else {
        return Ok(None);
    };

    let condition = encoder.encode_formula(condition)?;
    let condition = encoder.coerce_bool_operand(condition);
    let not_condition = encoder.solver_mut().not(condition);
    let then_case = encoder.solver_mut().and(condition, then_negated);
    let else_case = encoder.solver_mut().and(not_condition, else_negated);
    Ok(Some(encoder.solver_mut().or(then_case, else_case)))
}

fn encode_negated_match_with_scrutinee(
    encoder: &mut AYEncoder,
    arms: &[trust_wp_core::formula::MatchArm],
    scrutinee: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> Result<Term, EncodingError> {
    if let Some(term) =
        encode_negated_option_match_with_scrutinee(encoder, arms, scrutinee, logic_fns)?
    {
        return Ok(term);
    }

    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(scrutinee.clone()),
        arms: arms.to_vec(),
    };
    let term = encoder.encode_formula(&match_expr)?;
    let term = encoder.coerce_bool_operand(term);
    Ok(encoder.solver_mut().not(term))
}

fn selected_option_bool_match_arm_body(
    arms: &[trust_wp_core::formula::MatchArm],
    value: &PureExpr,
) -> Option<PureExpr> {
    let PureExpr::Bool(returned) = strip_let_assume(value) else {
        return None;
    };
    let returned = *returned;
    for arm in arms {
        match &arm.pattern {
            Pattern::Constructor { name, inner }
                if short_constructor_name(name) == "Some"
                    && option_bool_literal_pattern_matches(inner.as_deref(), returned) =>
            {
                return Some(arm.body.clone());
            }
            Pattern::Wildcard => return Some(arm.body.clone()),
            _ => {}
        }
    }
    None
}

fn option_bool_literal_pattern_matches(pattern: Option<&Pattern>, returned: bool) -> bool {
    matches!(pattern, Some(Pattern::Literal(PureExpr::Bool(lit))) if *lit == returned)
}

fn encode_negated_option_match_with_scrutinee(
    encoder: &mut AYEncoder,
    arms: &[trust_wp_core::formula::MatchArm],
    scrutinee: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> Result<Option<Term>, EncodingError> {
    let Some(match_arms) = option_match_postcondition_arms(arms) else {
        return Ok(None);
    };
    // Fix A decline: `^binding` on a possibly-&mut-embedding payload must not
    // take the collapsing shortcut — fall back to the general (guarded) path.
    if final_of_binding_requires_prophecy(match_arms.some_body, match_arms.some_binding) {
        return Ok(None);
    }

    let scrutinee = strip_let_assume(scrutinee).clone();
    let none_branch = encode_negated_postcondition(encoder, match_arms.none_body, logic_fns, None)?;

    let payload = PureExpr::MethodCall {
        receiver: Arc::new(scrutinee.clone()),
        method: "unwrap_logic".to_string(),
        args: vec![],
    };
    let some_body =
        substitute_match_binding_payload(match_arms.some_body, match_arms.some_binding, &payload);
    let some_branch = encode_negated_postcondition(encoder, &some_body, logic_fns, None)?;

    let is_none = PureExpr::MethodCall {
        receiver: Arc::new(scrutinee.clone()),
        method: "is_none".to_string(),
        args: vec![],
    };
    let is_some = PureExpr::MethodCall {
        receiver: Arc::new(scrutinee),
        method: "is_some".to_string(),
        args: vec![],
    };
    let is_none = encoder.encode_formula(&is_none)?;
    let is_none = encoder.coerce_bool_operand(is_none);
    let is_some = encoder.encode_formula(&is_some)?;
    let is_some = encoder.coerce_bool_operand(is_some);
    let none_case = encoder.solver_mut().and(is_none, none_branch);
    let some_case = encoder.solver_mut().and(is_some, some_branch);
    Ok(Some(encoder.solver_mut().or(none_case, some_case)))
}

fn selected_match_arm_body_for_expr(
    arms: &[trust_wp_core::formula::MatchArm],
    value: &PureExpr,
) -> Option<PureExpr> {
    for arm in arms {
        let mut substitutions = HashMap::new();
        if pattern_matches_value(&arm.pattern, value, &mut substitutions) {
            // Binder-erasing (#125): pattern bindings := matched payloads.
            return Some(arm.body.substitute_binder_erasing(&substitutions));
        }
    }
    None
}

fn pattern_matches_value(
    pattern: &Pattern,
    value: &PureExpr,
    substitutions: &mut HashMap<String, PureExpr>,
) -> bool {
    match pattern {
        Pattern::Wildcard => true,
        Pattern::Binding(name) => {
            substitutions.insert(name.clone(), value.clone());
            true
        }
        Pattern::Alias { alias, pattern } => {
            if !pattern_matches_value(pattern, value, substitutions) {
                return false;
            }
            substitutions.insert(alias.clone(), value.clone());
            true
        }
        Pattern::Literal(literal) => {
            crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(literal, value)
        }
        Pattern::Constructor { name, inner } => {
            let Some((value_ctor, value_args)) = constructor_value_parts(value) else {
                return false;
            };
            if short_constructor_name(name) != short_constructor_name(value_ctor) {
                return false;
            }
            match inner.as_deref() {
                None => value_args.is_empty(),
                Some(inner) if value_args.len() == 1 => {
                    pattern_matches_value(inner, &value_args[0], substitutions)
                }
                Some(_) => false,
            }
        }
        Pattern::Tuple(elements) => {
            let PureExpr::LogicFnCall { name, args } = value else {
                return false;
            };
            if trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_arity(name)
                != Some(elements.len())
            {
                return false;
            }
            elements.len() == args.len()
                && elements
                    .iter()
                    .zip(args)
                    .all(|(element, arg)| pattern_matches_value(element, arg, substitutions))
        }
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

fn constructor_value_parts(value: &PureExpr) -> Option<(&str, &[PureExpr])> {
    match value {
        PureExpr::LogicFnCall { name, args } => Some((name.as_str(), args.as_slice())),
        PureExpr::Var(name, _) if short_constructor_name(name) == "None" => {
            Some((name.as_str(), &[]))
        }
        _ => None,
    }
}

fn encode_ground_negated_existential_instance(
    encoder: &mut AYEncoder,
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> Result<Option<Term>, EncodingError> {
    let Some(return_expr) = return_expr else {
        return Ok(None);
    };
    let Some((var, body)) = top_level_existential_body(ensure) else {
        return Ok(None);
    };
    let Some(witness) = result_equality_existential_witness(var, body, return_expr) else {
        return Ok(None);
    };

    let mut substitutions = HashMap::new();
    substitutions.insert(var.to_string(), witness);
    // Binder-erasing (#125): the `exists` binder := its equality witness.
    // Normalising here also keeps the encoder's constant-carrier guard from
    // over-refusing a legitimately erased `^var`.
    let instantiated = body.substitute_binder_erasing(&substitutions);
    let body_term = encoder.encode_formula(&instantiated)?;
    let body_term = encoder.coerce_bool_operand(body_term);
    Ok(Some(encoder.solver_mut().not(body_term)))
}

fn top_level_existential_body(expr: &PureExpr) -> Option<(&str, &PureExpr)> {
    let PureExpr::Exists { var, body, .. } = expr else {
        return None;
    };
    Some((var.as_str(), body))
}

fn result_equality_existential_witness(
    var: &str,
    body: &PureExpr,
    return_expr: &PureExpr,
) -> Option<PureExpr> {
    let mut result_substitution = HashMap::new();
    result_substitution.insert("result".to_string(), return_expr.clone());
    let body = body.substitute(&result_substitution);
    for conjunct in top_level_conjunct_exprs(&body) {
        let PureExpr::BinOp(left, BinOp::Eq, right) = conjunct else {
            continue;
        };
        if let Some(witness) = result_equality_existential_witness_side(var, left, right) {
            return Some(witness);
        }
        if let Some(witness) = result_equality_existential_witness_side(var, right, left) {
            return Some(witness);
        }
    }
    None
}

fn result_equality_existential_witness_side(
    var: &str,
    candidate: &PureExpr,
    other: &PureExpr,
) -> Option<PureExpr> {
    if matches!(candidate, PureExpr::Var(name, _) if name == var) && !expr_has_var(other, var) {
        return Some(other.clone());
    }
    let Some((candidate_base, candidate_offset)) = split_base_plus_var(candidate, var) else {
        return None;
    };
    let Some((other_base, other_offset)) = split_base_plus_int(other) else {
        return None;
    };
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(candidate_base, other_base)
        .then(|| PureExpr::Int(other_offset - candidate_offset))
}

fn top_level_conjunct_exprs(expr: &PureExpr) -> Vec<&PureExpr> {
    let mut conjuncts = Vec::new();
    collect_top_level_conjuncts(expr, &mut conjuncts);
    conjuncts
}

fn expr_has_var(expr: &PureExpr, var: &str) -> bool {
    expr.free_vars().iter().any(|name| name == var)
}

fn split_base_plus_var<'a>(expr: &'a PureExpr, var: &str) -> Option<(&'a PureExpr, i64)> {
    match expr {
        PureExpr::Var(name, _) if name == var => Some((expr, 0)),
        PureExpr::BinOp(left, BinOp::Add, right) => {
            if matches!(right.as_ref(), PureExpr::Var(name, _) if name == var)
                && !expr_has_var(left, var)
            {
                return Some((left, 0));
            }
            if matches!(left.as_ref(), PureExpr::Var(name, _) if name == var)
                && !expr_has_var(right, var)
            {
                return Some((right, 0));
            }
            None
        }
        _ => None,
    }
}

fn split_base_plus_int(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    match expr {
        PureExpr::BinOp(left, BinOp::Add, right) => {
            if let PureExpr::Int(offset) = right.as_ref() {
                return Some((left, *offset));
            }
            if let PureExpr::Int(offset) = left.as_ref() {
                return Some((right, *offset));
            }
            None
        }
        PureExpr::BinOp(left, BinOp::Sub, right) => {
            let PureExpr::Int(offset) = right.as_ref() else {
                return None;
            };
            Some((left, offset.checked_neg()?))
        }
        _ => Some((expr, 0)),
    }
}

struct OptionMatchPostconditionArms<'a> {
    some_binding: &'a str,
    some_body: &'a PureExpr,
    none_body: &'a PureExpr,
}

struct OptionIteReturnBranches<'a> {
    condition: &'a PureExpr,
    some_payload: &'a PureExpr,
    some_when_condition: bool,
}

/// Recognize the `slice_first` proof shape before ay-dpll reaches native
/// datatype conflict analysis:
///
/// `match result { Some(v) => P(v), None => len == 0 }`
/// with body `if len > 0 { Some(payload) } else { None }`.
///
/// The shortcut only fires when substituting the Some payload makes the Some
/// arm trivially true and the None arm is the exact zero-length postcondition
/// implied by a positive sequence-length branch condition. Other Option matches
/// fall back to the normal encoded path.
fn encode_negated_result_match_over_option_ite(
    encoder: &mut AYEncoder,
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> Result<Option<Term>, EncodingError> {
    if result_match_over_option_ite_is_directly_valid(ensure, return_expr) {
        return Ok(Some(encoder.solver_mut().bool_const(false)));
    }
    Ok(None)
}

pub(in crate::verify) fn result_match_over_option_ite_is_directly_valid(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> bool {
    let PureExpr::Match { scrutinee, arms } = ensure else {
        return false;
    };
    if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result") {
        return false;
    }
    let Some(return_expr) = return_expr else {
        return false;
    };
    let Some(match_arms) = option_match_postcondition_arms(arms) else {
        return false;
    };
    let Some(branches) = option_ite_return_branches(return_expr) else {
        return false;
    };
    if !branches.some_when_condition {
        return false;
    }
    // Fix A decline: never accept via the shortcut when `^binding` needs a
    // prophecy slot — the collapse-based triviality check would be inverted.
    if final_of_binding_requires_prophecy(match_arms.some_body, match_arms.some_binding) {
        return false;
    }

    let some_post = substitute_match_binding_payload(
        match_arms.some_body,
        match_arms.some_binding,
        branches.some_payload,
    );
    is_trivially_true_postcondition(&some_post)
        && none_arm_len_zero_follows_nonempty_condition(match_arms.none_body, branches.condition)
}

pub(crate) fn result_match_over_option_ite_is_directly_invalid(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> bool {
    let PureExpr::Match { scrutinee, arms } = ensure else {
        return false;
    };
    if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result") {
        return false;
    }
    let Some(return_expr) = return_expr else {
        return false;
    };
    let Some(match_arms) = option_match_postcondition_arms(arms) else {
        return false;
    };
    let Some(branches) = option_ite_return_branches(return_expr) else {
        return false;
    };
    if !branches.some_when_condition {
        return false;
    }
    // Fix A decline: a collapse-based "definitely false" verdict over a
    // prophecy-needing `^binding` would be a fabricated rejection — decline.
    if final_of_binding_requires_prophecy(match_arms.some_body, match_arms.some_binding) {
        return false;
    }

    let some_post = substitute_match_binding_payload(
        match_arms.some_body,
        match_arms.some_binding,
        branches.some_payload,
    );
    is_definitely_false_postcondition(&some_post)
        || none_arm_len_value_conflicts_nonempty_condition(match_arms.none_body, branches.condition)
}

fn option_match_postcondition_arms(
    arms: &[trust_wp_core::formula::MatchArm],
) -> Option<OptionMatchPostconditionArms<'_>> {
    if arms.len() != 2 {
        return None;
    }
    let mut some: Option<(&str, &PureExpr)> = None;
    let mut none: Option<&PureExpr> = None;
    for arm in arms {
        let Pattern::Constructor { name, inner } = &arm.pattern else {
            return None;
        };
        match short_constructor_name(name) {
            "Some" => {
                let Some(Pattern::Binding(binding)) = inner.as_deref() else {
                    return None;
                };
                some = Some((binding.as_str(), &arm.body));
            }
            "None" => {
                if inner.is_some() {
                    return None;
                }
                none = Some(&arm.body);
            }
            _ => return None,
        }
    }
    let (some_binding, some_body) = some?;
    Some(OptionMatchPostconditionArms {
        some_binding,
        some_body,
        none_body: none?,
    })
}

fn option_ite_return_branches(return_expr: &PureExpr) -> Option<OptionIteReturnBranches<'_>> {
    let return_expr = strip_let_assume(return_expr);
    let PureExpr::Ite(condition, then_branch, else_branch) = return_expr else {
        return None;
    };

    let then_body = strip_let_assume(then_branch);
    let else_body = strip_let_assume(else_branch);

    match (
        option_some_payload(then_body),
        option_none_value(then_body),
        option_some_payload(else_body),
        option_none_value(else_body),
    ) {
        (Some(payload), _, _, Some(())) => Some(OptionIteReturnBranches {
            condition,
            some_payload: payload,
            some_when_condition: true,
        }),
        (_, Some(()), Some(payload), _) => Some(OptionIteReturnBranches {
            condition,
            some_payload: payload,
            some_when_condition: false,
        }),
        _ => None,
    }
}

fn strip_let_assume(expr: &PureExpr) -> &PureExpr {
    let mut current = expr;
    while let PureExpr::LetAssume { body, .. } = current {
        current = body;
    }
    current
}

fn option_some_payload(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    (short_constructor_name(name) == "Some" && args.len() == 1).then(|| &args[0])
}

fn option_none_value(expr: &PureExpr) -> Option<()> {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            (short_constructor_name(name) == "None" && args.is_empty()).then_some(())
        }
        PureExpr::Var(name, _) => (short_constructor_name(name) == "None").then_some(()),
        _ => None,
    }
}

/// Final-collapse audit Fix A (goal-side shortcut decline predicate): does the
/// arm body contain a `Final` (`^`) projection over the match binding whose
/// sort may embed a mutable reference?
///
/// The option-match shortcuts collapse `*b`/`^b` on the binder and substitute
/// the payload. That collapse is sort-blind — for a binder over an
/// `Option<&mut T>` payload it asserts the prophecy inversion `^b == *b`
/// (the adjudicated take_first_mut false accept). Registry-free layer: uses
/// the syntactic fail-closed variant (missing/unresolvable annotations count
/// as embedding). When this returns true the shortcut must DECLINE, letting
/// the general match-encoding path re-examine the expression under the
/// sort-aware encoder guard (honest error/Unknown, never a collapsed pass).
fn final_of_binding_requires_prophecy(body: &PureExpr, binding: &str) -> bool {
    use crate::encoder::final_collapse_guard::expr_sort_may_embed_mut_ref_syntactic;
    body.any_recursive(|node| {
        let PureExpr::Final(inner) = node else {
            return false;
        };
        inner.any_recursive(|sub| {
            matches!(
                sub,
                PureExpr::Var(name, ann)
                    if name == binding && expr_sort_may_embed_mut_ref_syntactic(ann.as_ref())
            )
        })
    })
}

fn substitute_match_binding_payload(
    body: &PureExpr,
    binding: &str,
    payload: &PureExpr,
) -> PureExpr {
    let mut bound = HashSet::new();
    bound.insert(binding);
    // #prophecy-slots (Fix B M4): this PureExpr-level shortcut runs before any
    // term exists for `binding`, so it has no term-level carrier knowledge and
    // passes the empty set — byte-identical legacy behaviour. The carrier case
    // is already governed here by `final_of_binding_requires_prophecy`, which
    // declines the shortcut outright.
    let collapsed = collapse_deref_for_bound_vars(body, &bound, &HashSet::new());
    let mut substitutions = HashMap::new();
    substitutions.insert(binding.to_string(), payload.clone());
    // Binder-erasing (#125): the match binding := its payload.
    collapsed.substitute_binder_erasing(&substitutions)
}

fn none_arm_len_zero_follows_nonempty_condition(
    none_body: &PureExpr,
    condition: &PureExpr,
) -> bool {
    let Some(condition_len) = positive_len_gt_zero_receiver(condition) else {
        return false;
    };
    let Some(none_len) = len_eq_zero_receiver(none_body) else {
        return false;
    };
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(condition_len, none_len)
}

fn none_arm_len_value_conflicts_nonempty_condition(
    none_body: &PureExpr,
    condition: &PureExpr,
) -> bool {
    let Some(condition_len) = positive_len_gt_zero_receiver(condition) else {
        return false;
    };
    let Some((none_len, value)) = len_eq_int_receiver(none_body) else {
        return false;
    };
    value > 0
        && crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
            condition_len,
            none_len,
        )
}

fn positive_len_gt_zero_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(lhs, op, rhs) = expr else {
        return None;
    };
    match op {
        BinOp::Gt if is_zero_literal(rhs) && is_len_call(lhs) => Some(lhs),
        BinOp::Lt if is_zero_literal(lhs) && is_len_call(rhs) => Some(rhs),
        _ => None,
    }
}

fn len_eq_zero_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    let (len, value) = len_eq_int_receiver(expr)?;
    (value == 0).then_some(len)
}

fn len_eq_int_receiver(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    if is_len_call(lhs) {
        let PureExpr::Int(value) = rhs.as_ref() else {
            return None;
        };
        Some((lhs, *value))
    } else if is_len_call(rhs) {
        let PureExpr::Int(value) = lhs.as_ref() else {
            return None;
        };
        Some((rhs, *value))
    } else {
        None
    }
}

fn is_len_call(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "len" && args.is_empty() && matches!(receiver.as_ref(), PureExpr::View(_))
    )
}

fn is_zero_literal(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Int(0))
}

/// Encode postcondition expressions and assert their negated conjunction.
///
/// Returns `Ok(false)` when `ensures` is empty (caller should return
/// `Verified` early). Returns `Ok(true)` when terms were asserted.
/// This consolidates the empty-check + encode + negate pattern used by
/// function.rs, mut_borrow.rs, and loops.rs (#785).
///
/// When any postcondition has a top-level existential quantifier, each
/// postcondition is negated individually (using PureExpr-level De Morgan
/// for existentials: `NOT(exists x. P(x))` → `forall x. NOT P(x)`) and the
/// results are combined with OR: `NOT(E1 AND E2) = NOT E1 OR NOT E2`.
/// This works around ay's E-matching limitation with negated existentials (#970).
pub(crate) fn encode_and_assert_negated_postconditions(
    encoder: &mut AYEncoder,
    ensures: &[PureExpr],
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    return_expr: Option<&PureExpr>,
) -> Result<bool, EncodingError> {
    // Reject postcondition/assertion expressions that are structurally non-boolean.
    // A bare integer (e.g., proof_assert!(1)) would crash ay's mk_not. (#1028)
    // Uses is_definitely_non_bool() to avoid rejecting ambiguous expressions
    // (Var(_, None), LogicFnCall) whose sort is unknown at parse time. (#1077)
    for expr in ensures {
        if is_definitely_non_bool(expr) {
            let sort = infer_expr_sort(expr);
            return Err(EncodingError::unsupported(format!(
                "postcondition/assertion must be boolean, got {sort:?}: {expr:?}"
            )));
        }
    }

    // Fast path: if no postcondition has any existential or universal quantifier,
    // use the standard approach (encode conjunction, negate at ay level).
    // Previously this only checked `matches!(e, PureExpr::Exists { .. })`, missing
    // nested existentials like `x > 0 && exists<i> f(i) == result`. (#1152)
    //
    // Also route to the slow path when postconditions mix universal quantifiers
    // with non-universal formulas. ay-dpll cannot handle `NOT(P AND forall<i>...)`
    // in the conjoined form — it needs the quantifier to be individually negated
    // and Skolemized at the PureExpr level. This fixes quantifier-unhandled on
    // patterns like `forall<i> 0<=i && i<v.len() ==> (^v)[i]==v[i]` combined
    // with non-quantifier postconditions in vector/09_capacity. (#2696)
    //
    // Also route all-universal sets with triggerless quantifiers to the slow
    // path (#1296). ay-dpll cannot handle `NOT(forall x. P(x))` when there
    // are no E-matching triggers. Skolemization at the PureExpr level converts
    // the negated universal to `NOT P(sk_x)`, keeping the problem quantifier-
    // free. This fixes quantifier-unhandled on tests where all postconditions
    // are triggerless universals (e.g., vector/09_capacity, result/own.rs).
    let has_existential = ensures
        .iter()
        .any(|e| matches!(e, PureExpr::Exists { .. }) || expr_contains_embedded_existential(e));
    let has_universal = ensures
        .iter()
        .any(|e| matches!(e, PureExpr::Forall { .. }) || expr_contains_embedded_universal(e));
    let has_non_universal = ensures
        .iter()
        .any(|e| !matches!(e, PureExpr::Forall { .. }));
    let mixed_universal = has_universal && has_non_universal;
    // Detect all-universal sets with triggerless quantifiers: these need
    // Skolemization because ay-dpll's E-matching has no triggers to work with.
    let all_universal_triggerless =
        has_universal && !has_non_universal && ensures.iter().all(|e| is_triggerless_universal(e));
    let route = classify_negated_postcondition_route(ensures);
    debug!(
        route = %route,
        has_existential,
        has_universal,
        has_non_universal,
        mixed_universal,
        all_universal_triggerless,
        ensures = ensures.len(),
        "selected negated-postcondition route"
    );
    if matches!(route, NegatedPostconditionRoute::Fast) {
        // Encode in Bool formula context so predicate lookups (Mapping
        // index_logic, etc.) are routed through Bool-context dispatch instead
        // of defaulting to Int sort. (#2245)
        // Trivially-true postcondition short-circuit (#2696): encode as
        // `true` directly to avoid triggering expensive logic function axiom
        // generation for reflexive equalities like `u(*a) == u(*a)`. In a
        // conjunction, `true` is the identity element and doesn't change the
        // result. The negation NOT(true AND rest) = NOT rest is correct.
        let mut terms: Vec<Term> = ensures
            .iter()
            .map(|e| {
                if is_trivially_true_postcondition(e) {
                    Ok(encoder.solver_mut().bool_const(true))
                } else if result_postcondition_matches_return_expr(e, return_expr, &[])
                    || super::function::result_binding::result_match_postcondition_directly_valid(
                        e,
                        return_expr,
                    )
                {
                    Ok(encoder.solver_mut().bool_const(true))
                } else if result_equals_return_expr_via_logic_body(e, logic_fns, return_expr) {
                    Ok(encoder.solver_mut().bool_const(true))
                } else if let Some(selected_body) =
                    selected_result_match_arm_body_for_return(e, return_expr)
                {
                    if is_trivially_true_postcondition(&selected_body)
                        || result_postcondition_matches_return_expr(
                            &selected_body,
                            return_expr,
                            &[],
                        )
                        || result_equals_return_expr_via_logic_body(
                            &selected_body,
                            logic_fns,
                            return_expr,
                        )
                    {
                        Ok(encoder.solver_mut().bool_const(true))
                    } else {
                        encoder.encode_formula(&selected_body)
                    }
                } else if let Some(inlined) = inline_result_logic_body_equality(e, logic_fns) {
                    encoder.encode_formula(&inlined)
                } else {
                    encoder.encode_formula(e)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        // Drain ALL division obligations (from body, precondition, AND postcondition
        // encoding) and conjoin with postconditions. NOT(ensures AND obligations) =
        // NOT ensures OR NOT obligations, so a zero divisor makes the overall check
        // SAT (= verification failure). Draining after encode_pure() captures
        // obligations from postcondition expressions like `result == x / y`. (#1629)
        let div_obligations = encoder.take_division_obligations();
        terms.extend(div_obligations);
        if terms.is_empty() {
            return Ok(false);
        }
        assert_negated_conjunction(encoder, terms);
        return Ok(true);
    }

    // Slow path: negate each postcondition individually and combine with OR.
    // NOT(E1 AND E2 AND ...) = NOT E1 OR NOT E2 OR ...
    // Reached when the route classifier selects a slow path:
    //   - mixed universal+non-universal
    //   - all-universal triggerless
    //   - existential-bearing postconditions
    // (#1296, #2696, #1152)
    // Delegates to encode_negated_postcondition which handles:
    //   - Top-level existentials: De Morgan + dual-form OR (#970, #1106)
    //   - Embedded existentials: witness instantiation (#1152)
    //   - Others: ay-level NOT
    // `all_universal_triggerless` is no longer propagated: Skolemization is
    // unconditional in the slow path of `encode_negated_postcondition`. The
    // local detects the routing condition so we still reach this branch for
    // all-universal-triggerless ensures (see block above). (#2696)
    let _ = all_universal_triggerless;
    let mut negated_terms: Vec<Term> = Vec::new();
    for e in ensures {
        let negated = encode_negated_postcondition(encoder, e, logic_fns, return_expr)?;
        negated_terms.push(negated);
    }

    // Drain division obligations AFTER postcondition encoding and negate them.
    // NOT(obligation) means "divisor could be zero" — one case suffices for SAT. (#1629)
    let div_obligations = encoder.take_division_obligations();
    for obligation in div_obligations {
        negated_terms.push(encoder.solver_mut().not(obligation));
    }

    if negated_terms.is_empty() {
        return Ok(false);
    }

    // Assert the disjunction: NOT E1 OR NOT E2 OR ... OR NOT O1 OR ...
    let disjunction = if negated_terms.len() == 1 {
        negated_terms.into_iter().next().expect("len checked == 1")
    } else {
        encoder.solver_mut().or_many(&negated_terms)
    };
    encoder.assert_term(disjunction);
    Ok(true)
}

#[cfg(test)]
mod tests {
    //! Unit tests for postcondition syntactic prechecks.
    //!
    //! Focus: shape extensions for `is_result_selector` and
    //! `normalize_result_logic_body_expr` covering the explicit
    //! `result.view()` method-call form (mirror of `result@` / `View(result)`),
    //! the `result.deep_model()` conversion (a function of its receiver, so
    //! stripping is sound by congruence), and the Creusot `*result` Deref form
    //! (likewise a deterministic projection — symmetric strip is sound). Phase
    //! 3 (B4) extension following commit 4a3dbe6 (deep_model) and cec1575.

    use std::sync::Arc;

    use trust_wp_core::{
        formula::{BinOp, PureExpr},
        logic::{LogicFnDef, LogicMode},
    };

    use super::{
        is_result_selector, logic_fn_equality_is_finite_enumerable_candidate,
        logic_fn_equality_is_projected_index_candidate, normalize_result_logic_body_expr,
        result_equals_return_expr_via_logic_body_with_requires,
    };

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn view(expr: PureExpr) -> PureExpr {
        PureExpr::View(Arc::new(expr))
    }

    fn view_method(expr: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(expr),
            method: "view".to_string(),
            args: vec![],
        }
    }

    fn deep_model_method(expr: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(expr),
            method: "deep_model".to_string(),
            args: vec![],
        }
    }

    fn deref(expr: PureExpr) -> PureExpr {
        PureExpr::Deref(Arc::new(expr))
    }

    fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
    }

    fn logic_call(name: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args,
        }
    }

    /// Build a logic function with body visible to callers (Open mode), as
    /// required by `logic_fn_body_visible` in the body-matcher precheck.
    fn open_logic_fn(name: &str, params: Vec<&str>, body: PureExpr) -> LogicFnDef {
        LogicFnDef::new(
            name.into(),
            format!("mod::{}", name),
            params.into_iter().map(String::from).collect(),
            body,
        )
        .with_mode(LogicMode::Open)
    }

    // --- is_result_selector ---

    #[test]
    fn is_result_selector_accepts_view_method_call() {
        // `result.view()` — the explicit method-call form of `result@`.
        assert!(is_result_selector(&view_method(var("result"))));
    }

    #[test]
    fn is_result_selector_accepts_view_method_call_nested_in_view() {
        // `result.view().view()` — still a chain of view wrappers.
        assert!(is_result_selector(&view_method(view_method(var("result")))));
    }

    #[test]
    fn is_result_selector_accepts_view_op_wrapped_around_view_method() {
        // `View(result.view())` — mixed parser/method form. Both are view ops.
        assert!(is_result_selector(&view(view_method(var("result")))));
    }

    #[test]
    fn is_result_selector_rejects_non_view_method_call() {
        // `result.into_inner()` — different method, NOT a view selector.
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(var("result")),
            method: "into_inner".to_string(),
            args: vec![],
        };
        assert!(!is_result_selector(&expr));
    }

    #[test]
    fn is_result_selector_rejects_view_method_with_args() {
        // `result.view(extra)` — view does not take args; not the identity form.
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(var("result")),
            method: "view".to_string(),
            args: vec![var("extra")],
        };
        assert!(!is_result_selector(&expr));
    }

    #[test]
    fn is_result_selector_rejects_view_method_on_non_result() {
        // `other.view()` — view of a non-result variable.
        assert!(!is_result_selector(&view_method(var("other"))));
    }

    // --- normalize_result_logic_body_expr strips .view() symmetrically ---

    #[test]
    fn normalize_strips_view_method_call() {
        // `x.view()` should normalize to `x`, matching the `View(x)` behavior.
        let normalized = normalize_result_logic_body_expr(&view_method(var("x")));
        assert_eq!(normalized, var("x"));
    }

    #[test]
    fn normalize_strips_chained_view_method_calls() {
        // `x.view().view()` should normalize to `x`.
        let normalized = normalize_result_logic_body_expr(&view_method(view_method(var("x"))));
        assert_eq!(normalized, var("x"));
    }

    #[test]
    fn normalize_preserves_non_view_method_call() {
        // `x.len()` should be preserved; only `.view()` is identity-stripped.
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(var("x")),
            method: "len".to_string(),
            args: vec![],
        };
        let normalized = normalize_result_logic_body_expr(&expr);
        assert_eq!(normalized, expr);
    }

    #[test]
    fn normalize_view_method_with_args_is_preserved() {
        // `x.view(extra)` — not the identity form, should not be stripped.
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(var("x")),
            method: "view".to_string(),
            args: vec![var("extra")],
        };
        let normalized = normalize_result_logic_body_expr(&expr);
        // `view` with args should be preserved as a MethodCall (its inner
        // operands may still be recursed into).
        assert_eq!(normalized, expr);
    }

    // --- end-to-end: result_equals_return_expr_via_logic_body_with_requires ---

    #[test]
    fn precheck_accepts_view_method_on_result_side() {
        // Postcondition: `result.view() == foo(a)` where foo body is `a@`.
        // Return expr: `x`. After substitution, expanded body is `View(x)`.
        // Both sides strip view → `x == x`. Match accepted.
        // Call site passes `x` as the argument to foo, so foo's parameter `a`
        // substitutes to `x` when we inline the body.
        let ensure = eq(
            view_method(var("result")),
            logic_call("foo", vec![var("x")]),
        );
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], view(var("a")))];
        let return_expr = var("x");

        assert!(result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    #[test]
    fn precheck_accepts_view_method_on_call_side_via_normalize() {
        // Postcondition: `result == foo(x)` where foo body is `a.view()`.
        // Substituting `a -> x` yields `x.view()`, which normalize_result_logic_body_expr
        // strips to `x`. Compared against return_expr=`x` → match accepted.
        let ensure = eq(var("result"), logic_call("foo", vec![var("x")]));
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], view_method(var("a")))];
        let return_expr = var("x");

        assert!(result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    #[test]
    fn precheck_rejects_view_method_on_result_with_mismatched_body() {
        // Postcondition: `result.view() == foo(a)` but foo body is `View(b)`,
        // a different parameter. After substitution `View(x_alt)` ≠ `View(x)`.
        let ensure = eq(
            view_method(var("result")),
            logic_call("foo", vec![var("a")]),
        );
        // Body references unrelated `b`, not parameter `a`.
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], view(var("b")))];
        let return_expr = var("x");

        // Body matches `View(b)` → `b`; return_expr is `x`; mismatch.
        assert!(!result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    #[test]
    fn precheck_rejects_non_view_method_on_result_side() {
        // Postcondition: `result.into_inner() == foo(a)`. `into_inner` is
        // NOT recognized as a result selector — should NOT match.
        let into_inner = PureExpr::MethodCall {
            receiver: Arc::new(var("result")),
            method: "into_inner".to_string(),
            args: vec![],
        };
        let ensure = eq(into_inner, logic_call("foo", vec![var("a")]));
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], var("a"))];
        let return_expr = var("x");

        assert!(!result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    // --- is_result_selector: deep_model() method form ---

    #[test]
    fn is_result_selector_accepts_deep_model_method_call() {
        // `result.deep_model()` — explicit Creusot deep-model conversion.
        assert!(is_result_selector(&deep_model_method(var("result"))));
    }

    #[test]
    fn is_result_selector_accepts_deep_model_method_nested_in_view() {
        // `View(result.deep_model())` — mixed view + deep_model wrappers.
        assert!(is_result_selector(&view(deep_model_method(var("result")))));
    }

    #[test]
    fn is_result_selector_accepts_view_method_nested_in_deep_model() {
        // `result.view().deep_model()` — chained view-then-deep_model.
        assert!(is_result_selector(&deep_model_method(view_method(var(
            "result"
        )))));
    }

    #[test]
    fn is_result_selector_rejects_deep_model_with_args() {
        // `result.deep_model(extra)` — deep_model is a zero-arg conversion;
        // an arg-bearing form is some unrelated user method.
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(var("result")),
            method: "deep_model".to_string(),
            args: vec![var("extra")],
        };
        assert!(!is_result_selector(&expr));
    }

    #[test]
    fn is_result_selector_rejects_deep_model_on_non_result() {
        // `other.deep_model()` — deep_model of a non-result variable.
        assert!(!is_result_selector(&deep_model_method(var("other"))));
    }

    // --- normalize_result_logic_body_expr strips .deep_model() symmetrically ---

    #[test]
    fn normalize_strips_deep_model_method_call() {
        // `x.deep_model()` should normalize to `x`, matching the `View` strip.
        let normalized = normalize_result_logic_body_expr(&deep_model_method(var("x")));
        assert_eq!(normalized, var("x"));
    }

    #[test]
    fn normalize_strips_chained_deep_model_method_calls() {
        // `x.deep_model().deep_model()` should normalize to `x`.
        let normalized =
            normalize_result_logic_body_expr(&deep_model_method(deep_model_method(var("x"))));
        assert_eq!(normalized, var("x"));
    }

    #[test]
    fn normalize_strips_mixed_view_and_deep_model() {
        // `x.view().deep_model()` and `x.deep_model().view()` both normalize
        // to `x` — view and deep_model are both stripped wrappers.
        let lhs = normalize_result_logic_body_expr(&deep_model_method(view_method(var("x"))));
        let rhs = normalize_result_logic_body_expr(&view_method(deep_model_method(var("x"))));
        assert_eq!(lhs, var("x"));
        assert_eq!(rhs, var("x"));
    }

    #[test]
    fn normalize_deep_model_with_args_is_preserved() {
        // `x.deep_model(extra)` — not the zero-arg form, should be preserved
        // as a MethodCall (only its operands are recursed into).
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(var("x")),
            method: "deep_model".to_string(),
            args: vec![var("extra")],
        };
        let normalized = normalize_result_logic_body_expr(&expr);
        assert_eq!(normalized, expr);
    }

    // --- end-to-end: result_equals_return_expr_via_logic_body_with_requires ---

    #[test]
    fn precheck_accepts_deep_model_on_result_side() {
        // Postcondition: `result.deep_model() == foo(a)` where foo body is
        // `a.deep_model()`. After substitution, expanded body is `x.deep_model()`.
        // Both sides strip deep_model → `x == x`. Match accepted.
        let ensure = eq(
            deep_model_method(var("result")),
            logic_call("foo", vec![var("x")]),
        );
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], deep_model_method(var("a")))];
        let return_expr = var("x");

        assert!(result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    #[test]
    fn precheck_accepts_deep_model_on_call_side_via_normalize() {
        // Postcondition: `result == foo(x)` where foo body is `a.deep_model()`.
        // Substituting `a -> x` yields `x.deep_model()`, which
        // normalize_result_logic_body_expr strips to `x`. Compared against
        // return_expr=`x` → match accepted.
        let ensure = eq(var("result"), logic_call("foo", vec![var("x")]));
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], deep_model_method(var("a")))];
        let return_expr = var("x");

        assert!(result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    #[test]
    fn precheck_accepts_mixed_view_and_deep_model_symmetric_strip() {
        // Postcondition: `result.view() == foo(x)` where foo body is
        // `a.deep_model()`. Stripping view from LHS gives `result`; stripping
        // deep_model from expanded body gives `x`. Both reduce to comparing
        // `result` (which is the result selector — equality between
        // return_expr and stripped body). return_expr=`x` → match.
        let ensure = eq(
            view_method(var("result")),
            logic_call("foo", vec![var("x")]),
        );
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], deep_model_method(var("a")))];
        let return_expr = var("x");

        assert!(result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    #[test]
    fn precheck_rejects_deep_model_with_mismatched_body() {
        // Postcondition: `result.deep_model() == foo(a)` but foo body
        // references `b`, a different variable. Expansion gives `b.deep_model()`,
        // which strips to `b`; return_expr is `x`. Mismatch.
        let ensure = eq(
            deep_model_method(var("result")),
            logic_call("foo", vec![var("a")]),
        );
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], deep_model_method(var("b")))];
        let return_expr = var("x");

        assert!(!result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    // --- is_result_selector: `*result` (Deref) form ---

    #[test]
    fn is_result_selector_accepts_deref() {
        // `*result` — the Creusot deref form (current value of a borrow).
        assert!(is_result_selector(&deref(var("result"))));
    }

    #[test]
    fn is_result_selector_accepts_chained_deref() {
        // `**result` — still resolves to the result selector.
        assert!(is_result_selector(&deref(deref(var("result")))));
    }

    #[test]
    fn is_result_selector_accepts_deref_nested_in_view() {
        // `View(*result)` — view wrapper around a deref of result.
        assert!(is_result_selector(&view(deref(var("result")))));
    }

    #[test]
    fn is_result_selector_accepts_view_method_nested_in_deref() {
        // `*result.view()` — deref outside, view method inside.
        assert!(is_result_selector(&deref(view_method(var("result")))));
    }

    #[test]
    fn is_result_selector_accepts_deep_model_nested_in_deref() {
        // `*result.deep_model()` — deref outside, deep_model method inside.
        assert!(is_result_selector(&deref(deep_model_method(var("result")))));
    }

    #[test]
    fn is_result_selector_rejects_deref_on_non_result() {
        // `*other` — deref of a non-result variable.
        assert!(!is_result_selector(&deref(var("other"))));
    }

    // --- normalize_result_logic_body_expr strips `Deref` symmetrically ---

    #[test]
    fn normalize_strips_deref() {
        // `*x` should normalize to `x`, matching the `View` / `deep_model` strip.
        let normalized = normalize_result_logic_body_expr(&deref(var("x")));
        assert_eq!(normalized, var("x"));
    }

    #[test]
    fn normalize_strips_chained_deref() {
        // `**x` should normalize to `x`.
        let normalized = normalize_result_logic_body_expr(&deref(deref(var("x"))));
        assert_eq!(normalized, var("x"));
    }

    #[test]
    fn normalize_strips_mixed_deref_view_and_deep_model() {
        // `*x.view()`, `*x.deep_model()`, and `View(*x)` all normalize to `x`.
        let a = normalize_result_logic_body_expr(&deref(view_method(var("x"))));
        let b = normalize_result_logic_body_expr(&deref(deep_model_method(var("x"))));
        let c = normalize_result_logic_body_expr(&view(deref(var("x"))));
        assert_eq!(a, var("x"));
        assert_eq!(b, var("x"));
        assert_eq!(c, var("x"));
    }

    #[test]
    fn normalize_strips_deref_inside_binop() {
        // `*x + *y` should normalize to `x + y` — Deref strip is structural and
        // applies under arithmetic operators (the matcher relies on this to
        // cancel `*` symmetrically on both sides of an equality body).
        let expr = PureExpr::BinOp(
            Arc::new(deref(var("x"))),
            BinOp::Add,
            Arc::new(deref(var("y"))),
        );
        let normalized = normalize_result_logic_body_expr(&expr);
        let expected = PureExpr::BinOp(Arc::new(var("x")), BinOp::Add, Arc::new(var("y")));
        assert_eq!(normalized, expected);
    }

    // --- end-to-end: result_equals_return_expr_via_logic_body_with_requires ---

    #[test]
    fn precheck_accepts_deref_on_result_side() {
        // Postcondition: `*result == foo(x)` where foo body is `*a`. After
        // substitution `a -> x`, expanded body is `*x`. Both sides strip Deref
        // → `x == x`. Match accepted (the selector accepts `*result`, and
        // normalization cancels the `*` on the call-side body too).
        let ensure = eq(deref(var("result")), logic_call("foo", vec![var("x")]));
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], deref(var("a")))];
        let return_expr = var("x");

        assert!(result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    #[test]
    fn precheck_accepts_deref_on_call_side_via_normalize() {
        // Postcondition: `result == foo(x)` where foo body is `*a`.
        // Substituting `a -> x` yields `*x`, which normalize strips to `x`.
        // Compared against return_expr=`x` → match accepted.
        let ensure = eq(var("result"), logic_call("foo", vec![var("x")]));
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], deref(var("a")))];
        let return_expr = var("x");

        assert!(result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    #[test]
    fn precheck_accepts_mixed_deref_and_view_symmetric_strip() {
        // Postcondition: `*result == foo(x)` where foo body is `a.view()`.
        // LHS strips to `result`; expanded body strips to `x`. Compared via
        // result-selector path against return_expr=`x` → match accepted.
        let ensure = eq(deref(var("result")), logic_call("foo", vec![var("x")]));
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], view_method(var("a")))];
        let return_expr = var("x");

        assert!(result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    #[test]
    fn precheck_rejects_deref_with_mismatched_body() {
        // Postcondition: `*result == foo(a)` but foo body references `b`.
        // Expansion gives `*b`, which strips to `b`; return_expr is `x`.
        // Mismatch.
        let ensure = eq(deref(var("result")), logic_call("foo", vec![var("a")]));
        let logic_fns = vec![open_logic_fn("foo", vec!["a"], deref(var("b")))];
        let return_expr = var("x");

        assert!(!result_equals_return_expr_via_logic_body_with_requires(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
            &[],
        ));
    }

    // --- logic_fn_equality_is_finite_enumerable_candidate (#popcount) ---

    use trust_wp_core::formula::UnOp as TestUnOp;

    fn int(v: i64) -> PureExpr {
        PureExpr::Int(v)
    }

    fn bitand(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::BitAnd, Arc::new(rhs))
    }

    fn add(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Add, Arc::new(rhs))
    }

    fn ite(cond: PureExpr, then_branch: PureExpr, else_branch: PureExpr) -> PureExpr {
        PureExpr::Ite(Arc::new(cond), Arc::new(then_branch), Arc::new(else_branch))
    }

    /// `count8_log`-style body: a sum of `if n & mask == 0 { 0 } else { 1 }`
    /// per-bit terms — a pure finite-domain integer/bitwise expression.
    fn popcount_style_body() -> PureExpr {
        let bit = |mask: i64| {
            ite(
                PureExpr::BinOp(
                    Arc::new(bitand(var("n"), int(mask))),
                    BinOp::Eq,
                    Arc::new(int(0)),
                ),
                int(0),
                int(1),
            )
        };
        add(add(bit(1), bit(2)), bit(4))
    }

    #[test]
    fn finite_enumerable_accepts_popcount_style_equality() {
        // `result@ == popcount_log(n)` over a non-recursive, finite-domain body
        // with a concrete return_expr is a finite-enumerable routing candidate.
        let ensure = eq(
            view(var("result")),
            logic_call("popcount_log", vec![var("n")]),
        );
        let logic_fns = vec![open_logic_fn(
            "popcount_log",
            vec!["n"],
            popcount_style_body(),
        )];
        let return_expr = bitand(var("n"), int(15));
        assert!(logic_fn_equality_is_finite_enumerable_candidate(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
        ));
    }

    #[test]
    fn finite_enumerable_rejects_without_return_expr() {
        // No concrete return_expr: nothing for the solver to bind `result` to.
        let ensure = eq(
            view(var("result")),
            logic_call("popcount_log", vec![var("n")]),
        );
        let logic_fns = vec![open_logic_fn(
            "popcount_log",
            vec!["n"],
            popcount_style_body(),
        )];
        assert!(!logic_fn_equality_is_finite_enumerable_candidate(
            &ensure,
            Some(&logic_fns),
            None,
        ));
    }

    #[test]
    fn finite_enumerable_rejects_recursive_logic_fn() {
        // A recursive logic fn is NOT decidable by the finite-enumeration bridge;
        // it must keep bailing to Unknown rather than being routed to the solver.
        let ensure = eq(view(var("result")), logic_call("rec_fn", vec![var("n")]));
        let mut logic_fn = open_logic_fn("rec_fn", vec!["n"], popcount_style_body());
        logic_fn.set_is_recursive(true);
        let return_expr = bitand(var("n"), int(15));
        assert!(!logic_fn_equality_is_finite_enumerable_candidate(
            &ensure,
            Some(&[logic_fn]),
            Some(&return_expr),
        ));
    }

    #[test]
    fn finite_enumerable_rejects_opaque_logic_fn() {
        let ensure = eq(view(var("result")), logic_call("opaque_fn", vec![var("n")]));
        let logic_fn =
            open_logic_fn("opaque_fn", vec!["n"], popcount_style_body()).with_opaque(true);
        let return_expr = bitand(var("n"), int(15));
        assert!(!logic_fn_equality_is_finite_enumerable_candidate(
            &ensure,
            Some(&[logic_fn]),
            Some(&return_expr),
        ));
    }

    #[test]
    fn finite_enumerable_rejects_non_arithmetic_body() {
        // Body contains a nested logic-fn call: not a pure finite-domain
        // integer/bitwise expression, so the enumeration bridge cannot decide it.
        let body = add(var("n"), logic_call("other", vec![var("n")]));
        let ensure = eq(view(var("result")), logic_call("wrap", vec![var("n")]));
        let logic_fns = vec![open_logic_fn("wrap", vec!["n"], body)];
        let return_expr = var("n");
        assert!(!logic_fn_equality_is_finite_enumerable_candidate(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
        ));
    }

    #[test]
    fn finite_enumerable_rejects_body_with_method_call() {
        // `result@ == wrap(s)` where wrap inlines `s.len()` (a method call) is not
        // a pure integer/bitwise body, so it stays out of the enumeration route.
        let body = PureExpr::MethodCall {
            receiver: Arc::new(var("s")),
            method: "len".to_string(),
            args: vec![],
        };
        let ensure = eq(view(var("result")), logic_call("wrap", vec![var("s")]));
        let logic_fns = vec![open_logic_fn("wrap", vec!["s"], body)];
        let return_expr = var("s");
        assert!(!logic_fn_equality_is_finite_enumerable_candidate(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
        ));
    }

    #[test]
    fn projected_index_accepts_memory_index_logic_shape() {
        // `*result == index_logic(self, i)` where the body is `self.0[i]`
        // (builtin index over a tuple-field projection of a param): route to
        // the solver (list_reversal_lasso). (#index_logic)
        let body = PureExpr::MethodCall {
            receiver: Arc::new(logic_call("__trust_wp_tuple_get_0", vec![var("self")])),
            method: "index_logic".to_string(),
            args: vec![var("i")],
        };
        let ensure = eq(
            PureExpr::Deref(Arc::new(var("result"))),
            logic_call("index_logic", vec![var("self"), var("i")]),
        );
        let logic_fns = vec![open_logic_fn("index_logic", vec!["self", "i"], body)];
        assert!(logic_fn_equality_is_projected_index_candidate(
            &ensure,
            Some(&logic_fns),
        ));
    }

    #[test]
    fn projected_index_rejects_recursive_fn_and_non_projection_bodies() {
        let projected_body = PureExpr::MethodCall {
            receiver: Arc::new(logic_call("__trust_wp_tuple_get_0", vec![var("self")])),
            method: "index_logic".to_string(),
            args: vec![var("i")],
        };
        let ensure = eq(
            PureExpr::Deref(Arc::new(var("result"))),
            logic_call("index_logic", vec![var("self"), var("i")]),
        );
        // Recursive fn: stays on the Unknown short-circuit.
        let mut recursive = open_logic_fn("index_logic", vec!["self", "i"], projected_body);
        recursive.set_is_recursive(true);
        assert!(!logic_fn_equality_is_projected_index_candidate(
            &ensure,
            Some(&[recursive]),
        ));
        // Non-projection receiver (raw param): not the accessor class.
        let raw_body = PureExpr::MethodCall {
            receiver: Arc::new(var("self")),
            method: "index_logic".to_string(),
            args: vec![var("i")],
        };
        let raw = open_logic_fn("index_logic", vec!["self", "i"], raw_body);
        assert!(!logic_fn_equality_is_projected_index_candidate(
            &ensure,
            Some(&[raw]),
        ));
    }

    #[test]
    fn finite_enumerable_rejects_unop_bitnot_body_still_enumerable() {
        // Bitwise complement IS enumerable; confirm UnOp::BitNot is accepted.
        let body = PureExpr::UnOp(TestUnOp::BitNot, Arc::new(var("n")));
        let ensure = eq(view(var("result")), logic_call("inv", vec![var("n")]));
        let logic_fns = vec![open_logic_fn("inv", vec!["n"], body)];
        let return_expr = var("n");
        assert!(logic_fn_equality_is_finite_enumerable_candidate(
            &ensure,
            Some(&logic_fns),
            Some(&return_expr),
        ));
    }
}
