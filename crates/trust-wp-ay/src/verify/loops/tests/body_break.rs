// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// -----------------------------------------------------------------------
// body-break condition_is_body_break tests (#1295 algorithm audit)
// -----------------------------------------------------------------------

pub(super) fn i_var() -> PureExpr {
    PureExpr::Var("i".to_string(), None)
}

pub(super) fn n_var() -> PureExpr {
    PureExpr::Var("n".to_string(), None)
}

pub(super) fn i_lt_n() -> PureExpr {
    PureExpr::BinOp(Arc::new(i_var()), BinOp::Lt, Arc::new(n_var()))
}

pub(super) fn i_le_n() -> PureExpr {
    PureExpr::BinOp(Arc::new(i_var()), BinOp::Le, Arc::new(n_var()))
}

pub(super) fn i_ge_zero() -> PureExpr {
    PureExpr::BinOp(Arc::new(i_var()), BinOp::Ge, Arc::new(PureExpr::Int(0)))
}

pub(super) fn n_ge(min: i64) -> PureExpr {
    PureExpr::BinOp(Arc::new(n_var()), BinOp::Ge, Arc::new(PureExpr::Int(min)))
}

pub(super) fn i_effect(step: i64) -> HashMap<String, PureExpr> {
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(Arc::new(i_var()), BinOp::Add, Arc::new(PureExpr::Int(step))),
    );
    body_effect
}

pub(super) fn modified_i() -> Vec<&'static str> {
    vec!["i"]
}

/// Preservation with `condition_is_body_break: true` must apply the
/// condition to primed (post-body) variables.
///
/// Models: `loop { i = i + 1; if i >= n { break; } }`
/// Invariant: i <= n
/// Body effect: i' = i + 1
/// Condition (continuation): i < n  (negation of break cond `i >= n`)
///
/// With body-break priming, the continuation condition becomes `i' < n`,
/// i.e. `(i+1) < n`. The VC is:
///   i <= n ∧ (i+1) < n => (i+1) <= n  → VALID (sound)
#[test]
#[timeout(30000)]
fn verify_preservation_body_break_basic() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Le,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    )];
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        true, // body-break: condition checked after body
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("body-break preservation should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "body-break preservation with i <= n should verify, got {result:?}"
    );
}

/// Preservation with body-break step=2: primed vs unprimed matters.
///
/// Models: `loop { i = i + 2; if i >= n { break; } }`
/// Invariant: i <= n
/// Body effect: i' = i + 2
///
/// With body-break priming: i <= n ∧ (i+2) < n => (i+2) <= n → VALID
/// Without priming (bug): i <= n ∧ i < n => (i+2) <= n → INVALID
#[test]
#[timeout(30000)]
fn verify_preservation_body_break_priming_matters() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Le,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    )];
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(2)),
        ),
    );

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        true, // body-break
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("body-break preservation should encode");

    // With correct priming: (i+2) < n ∧ i <= n => (i+2) <= n → VALID
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "body-break preservation with step=2 should verify with primed condition, got {result:?}"
    );
}

/// Contrast: header-condition with step=2 should FAIL because the
/// unprimed condition (i < n) is too weak to guarantee i+2 <= n.
///
/// Counterexample: i = n-1, n >= 1 → i < n ∧ i <= n → (i+2) <= n is FALSE
#[test]
#[timeout(30000)]
fn verify_preservation_header_condition_step2_fails() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Le,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    )];
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(2)),
        ),
    );

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        false, // header condition: NOT body-break
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("header-condition preservation should encode");

    // Header condition: i < n ∧ i <= n => (i+2) <= n → INVALID
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "header-condition preservation with step=2 should FAIL, got {result:?}"
    );
}

/// Full pipeline test with `condition_is_body_break: true` via
/// `verify_loop_invariant`. Confirms init and preservation VCs pass for
/// a body-break loop routed through the full pipeline.
///
/// Models: `let mut i = 0; loop { i += 1; if i >= n { break } }`
/// Requires: n > 0
/// Invariant: 0 <= i ∧ i < n
///
/// The invariant uses `i < n` (strict) because `i == n` at loop head is
/// unreachable: the break fires when the post-body `i` reaches `n`.
/// Postcondition body-break priming is tested separately in
/// `verify_postcondition_body_break_primes_exit_condition`. (#1385)
#[test]
#[timeout(30000)]
fn verify_loop_invariant_body_break_full_pipeline() {
    let requires = vec![PureExpr::BinOp(
        Arc::new(n_var()),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    let invariants = vec![i_ge_zero(), i_lt_n()];
    let modified_vars = modified_i();
    let body_effect = i_effect(1);
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&i_lt_n()),
        condition_is_body_break: true,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("body-break loop verification should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization should verify, got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify with body-break priming, got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition (vacuously true, no ensures) should verify, got {:?}",
        result.postcondition
    );
}

/// Postcondition for body-break loops must negate the continuation condition
/// over post-body state (primed variables), not pre-body state.
///
/// This test uses `result != n + 1` to distinguish primed vs unprimed exit
/// condition handling:
/// - Primed exit (`i' >= n`) allows `i = n - 1`, `i' = n + 1`, violating
///   the postcondition, so the VC must fail.
/// - Unprimed exit (`i >= n`) forces `i = n` (with invariant `i <= n`),
///   making `i' = n + 2`; the same violation is no longer reachable.
#[test]
#[timeout(30000)]
fn verify_postcondition_body_break_primes_exit_condition() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Le,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    )];
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Ne,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    )];
    let return_expr = PureExpr::Var("i".to_string(), None);
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(2)),
        ),
    );

    let result = verify_postcondition(
        &invariants,
        Some(&loop_condition),
        true,
        &modified_vars,
        postcondition_inputs(&ensures, Some(&return_expr), &HashMap::new(), &[], &[]),
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("body-break postcondition should encode");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "primed exit condition should expose counterexample (i = n - 1 => i' = n + 1), \
         got {result:?}"
    );
}

/// Body-break variant non-negativity must be guarded by the primed
/// continuation condition (`i + step < n`).
#[test]
#[timeout(30000)]
fn verify_variant_nonneg_body_break_primes_condition() {
    let invariants = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Le,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(3)),
        ),
    ];
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let variant = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".to_string(), None)),
            BinOp::Sub,
            Arc::new(PureExpr::Var("i".to_string(), None)),
        )),
        BinOp::Sub,
        Arc::new(PureExpr::Int(2)),
    );
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(2)),
        ),
    );

    let header_nonneg = verify_variant_nonneg(
        &invariants,
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("header variant nonneg should encode");
    assert!(
        matches!(header_nonneg, VerificationResult::Failed(_)),
        "header-guarded nonneg should fail, got {header_nonneg:?}"
    );

    let body_break_nonneg = verify_variant_nonneg(
        &invariants,
        Some(&loop_condition),
        true,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("body-break variant nonneg should encode");
    assert!(
        matches!(body_break_nonneg, VerificationResult::Verified(_)),
        "body-break nonneg should verify with primed condition, got {body_break_nonneg:?}"
    );
}

/// Body-break variant decrease must also use the primed continuation
/// condition; otherwise boundary states can produce false failures.
#[test]
#[timeout(30000)]
fn verify_variant_decrease_body_break_primes_condition() {
    let invariants = vec![i_ge_zero(), i_le_n(), n_ge(4)];
    let loop_condition = i_lt_n();
    let i_equals_n_minus_one = PureExpr::BinOp(
        Arc::new(i_var()),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(n_var()),
            BinOp::Sub,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    let variant = PureExpr::Ite(
        Arc::new(i_equals_n_minus_one),
        Arc::new(PureExpr::Int(-10)),
        Arc::new(PureExpr::BinOp(
            Arc::new(n_var()),
            BinOp::Sub,
            Arc::new(i_var()),
        )),
    );
    let modified_vars = modified_i();
    let body_effect = i_effect(2);

    let header_decrease = verify_variant_decrease(
        &invariants,
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("header variant decrease should encode");
    assert!(
        matches!(header_decrease, VerificationResult::Failed(_)),
        "header-guarded decrease should fail, got {header_decrease:?}"
    );

    let body_break_decrease = verify_variant_decrease(
        &invariants,
        Some(&loop_condition),
        true,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("body-break variant decrease should encode");
    assert!(
        matches!(body_break_decrease, VerificationResult::Verified(_)),
        "body-break decrease should verify with primed condition, got {body_break_decrease:?}"
    );
}

/// Body-break variant nonneg vacuity guard must use the primed condition.
///
/// Setup: invariant pins `i == n - 1` with `n >= 1`, condition is `i < n`,
/// body effect `i := i + 2`, variant is constant `-1`.
///
/// - Unprimed condition: `n - 1 < n` — satisfiable (base not vacuous).
/// - Primed condition: `(n - 1 + 2) < n` → `n + 1 < n` — UNSAT (base vacuous).
///
/// The negated goal (`variant < 0`) is trivially satisfiable (variant = -1),
/// so without vacuity detection the result would be `Failed`.
///
/// Header-conditioned call: base not vacuous → `Failed`.
/// Body-break call: primed base vacuous → `Unknown(vacuous)`.
#[test]
#[timeout(30000)]
fn verify_variant_nonneg_body_break_vacuity_uses_primed_condition() {
    let i_eq_n_minus_1 = PureExpr::BinOp(
        Arc::new(i_var()),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(n_var()),
            BinOp::Sub,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    let invariants = vec![i_eq_n_minus_1, n_ge(1)];
    let loop_condition = i_lt_n();
    let variant = PureExpr::Int(-1); // constant negative
    let modified_vars = modified_i();
    let body_effect = i_effect(2);

    // Header condition: unprimed base is satisfiable → vacuity guard does not
    // fire → negated goal (variant < 0 is true) is SAT → Failed.
    let header_result = verify_variant_nonneg(
        &invariants,
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("header variant nonneg should encode");
    assert!(
        matches!(header_result, VerificationResult::Failed(_)),
        "header-conditioned nonneg with constant -1 variant should fail, got {header_result:?}"
    );

    // Body-break: primed base (n+1 < n) is UNSAT → vacuity guard fires →
    // Unknown(vacuous).
    let body_break_result = verify_variant_nonneg(
        &invariants,
        Some(&loop_condition),
        true,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("body-break variant nonneg should encode");
    assert!(
        matches!(
            body_break_result,
            VerificationResult::Unknown(UnknownReason::SolverMessage(ref msg))
            if msg.contains("vacuous")
        ),
        "body-break nonneg with vacuous primed base should return Unknown(vacuous), \
         got {body_break_result:?}"
    );
}

/// Body-break variant decrease vacuity guard must use the primed condition.
///
/// Same setup as the nonneg vacuity test but with a constant variant (5) so
/// the negated goal (`variant' >= variant` → `5 >= 5`) is trivially SAT.
///
/// Header-conditioned call: base not vacuous → `Failed`.
/// Body-break call: primed base vacuous → `Unknown(vacuous)`.
#[test]
#[timeout(30000)]
fn verify_variant_decrease_body_break_vacuity_uses_primed_condition() {
    let i_eq_n_minus_1 = PureExpr::BinOp(
        Arc::new(i_var()),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(n_var()),
            BinOp::Sub,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    let invariants = vec![i_eq_n_minus_1, n_ge(1)];
    let loop_condition = i_lt_n();
    let variant = PureExpr::Int(5); // constant (does not decrease)
    let modified_vars = modified_i();
    let body_effect = i_effect(2);

    // Header condition: unprimed base is satisfiable → vacuity guard does not
    // fire → negated goal (variant' >= variant → 5 >= 5) is SAT → Failed.
    let header_result = verify_variant_decrease(
        &invariants,
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("header variant decrease should encode");
    assert!(
        matches!(header_result, VerificationResult::Failed(_)),
        "header-conditioned decrease with constant variant should fail, got {header_result:?}"
    );

    // Body-break: primed base (n+1 < n) is UNSAT → vacuity guard fires →
    // Unknown(vacuous).
    let body_break_result = verify_variant_decrease(
        &invariants,
        Some(&loop_condition),
        true,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("body-break variant decrease should encode");
    assert!(
        matches!(
            body_break_result,
            VerificationResult::Unknown(UnknownReason::SolverMessage(ref msg))
            if msg.contains("vacuous")
        ),
        "body-break decrease with vacuous primed base should return Unknown(vacuous), \
         got {body_break_result:?}"
    );
}

/// Body-break preservation with no condition: the body-break flag is
/// irrelevant when there's no condition to prime.
#[test]
#[timeout(30000)]
fn verify_preservation_body_break_no_condition() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let modified_vars: Vec<&str> = vec!["x"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "x".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let result = verify_preservation_with_config(
        &invariants,
        None, // no condition
        true, // body-break flag set but irrelevant
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("conditionless body-break preservation should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "preservation with no condition should verify, got {result:?}"
    );
}

/// Body-break preservation vacuity guard must use the primed condition (#2628).
///
/// Setup: invariant pins `i == n - 1` with `n >= 1`, condition is `i < n`,
/// body effect `i := i + 2`.
///
/// - Unprimed condition: `(n - 1) < n` — satisfiable (base not vacuous).
/// - Primed condition: `(n + 1) < n` — UNSAT with invariant + effect equality.
///
/// The preservation VC base is vacuous only in the body-break lane. We use a
/// second invariant `i >= 0` that the effect violates (i + 2 can exceed n)
/// so the negated postcondition is satisfiable — without vacuity detection the
/// result would be `Failed` (or `Verified` vacuously).
///
/// Header-conditioned call: base not vacuous → `Failed`.
/// Body-break call: primed base vacuous → `Unknown(vacuous)`.
#[test]
#[timeout(30000)]
fn verify_preservation_body_break_vacuity_uses_primed_condition() {
    let i_eq_n_minus_1 = PureExpr::BinOp(
        Arc::new(i_var()),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(n_var()),
            BinOp::Sub,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    let invariants = vec![i_eq_n_minus_1, n_ge(1), i_ge_zero()];
    let loop_condition = i_lt_n();
    let modified_vars = modified_i();
    let body_effect = i_effect(2);

    // Header condition: unprimed base is satisfiable → vacuity guard does not
    // fire → preservation check runs normally.
    let header_result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        false, // header condition
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("header preservation should encode");
    assert!(
        !matches!(
            header_result,
            VerificationResult::Unknown(UnknownReason::SolverMessage(ref msg))
            if msg.contains("vacuous")
        ),
        "header-conditioned preservation should NOT be vacuous, got {header_result:?}"
    );

    // Body-break: primed base (n+1 < n) is UNSAT → vacuity guard fires →
    // Unknown(vacuous).
    let body_break_result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        true, // body-break
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("body-break preservation should encode");
    assert!(
        matches!(
            body_break_result,
            VerificationResult::Unknown(UnknownReason::SolverMessage(ref msg))
            if msg.contains("vacuous")
        ),
        "body-break preservation with vacuous primed base should return Unknown(vacuous), \
         got {body_break_result:?}"
    );
}
