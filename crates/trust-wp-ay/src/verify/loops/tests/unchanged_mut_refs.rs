// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// --- Phase 4 unchanged mut ref borrow resolution tests (#759) ---

/// Phase 4 borrow resolution: unchanged `&mut bool` parameter's prophecy
/// resolves to its current value at loop exit. When `*y == true` is a
/// precondition and `y` is NOT modified by the loop body, the postcondition
/// `^y == true` (Final(Var("y"))) must verify because Phase 4 asserts
/// `y_final == y_current` (postcondition.rs:339-358).
///
/// This exercises the Phase 4 path exclusively — the existing test
/// `verify_postcondition_borrow_resolution_bool_deref_effect` covers the
/// deref_body_effect path (Phase 3) but not this unchanged-mut-ref path.
///
/// Re: #759 — Phase 4 borrow resolution for unchanged mutable reference parameters
#[test]
#[timeout(30000)]
fn verify_postcondition_unchanged_mut_ref_bool_borrow_resolves() {
    // Scenario: fn preserve(y: &mut bool, n: i32) with loop { i += 1 }
    // y is NOT modified by the loop body — only i changes.
    // Precondition: *y == true (y_current == true at function entry)
    // Invariant: i >= 0 ∧ i <= n (trivial loop bound)
    // Postcondition: ^y == true (Final(Var("y")) == true)
    //
    // Phase 4 should assert y_final == y_current, which combined with
    // the unmodified-parameter require (*y == true) proves ^y == true.
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "y".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Bool))),
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Bool(true)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "y".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Bool))),
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Bool(true)),
    )];
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
    let mut pre_loop = HashMap::new();
    pre_loop.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };

    let result = verify_postcondition(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &pre_loop, &requires, &[]),
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("postcondition encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Phase 4 borrow resolution should prove ^y == true for unchanged &mut bool. \
         Got {result:?}. If Failed, Phase 4 (postcondition.rs:339-358) is not asserting \
         y_final == y_current for unchanged mut ref parameters."
    );
}

/// Pipeline sanity check: unchanged `&mut bool` parameter's prophecy
/// cannot satisfy a postcondition that contradicts the precondition.
/// When `*y == true` is a require, `^y == false` must FAIL.
///
/// NOTE: This test passes regardless of whether Phase 4 is present.
/// Without Phase 4, `y_final` is unconstrained and the solver trivially
/// finds a counterexample (`y_final = true`) for the negated postcondition.
/// With Phase 4, `y_final == y_current == true` also contradicts `^y == false`.
/// The two positive tests (`_bool_borrow_resolves`, `_int_borrow_resolves`)
/// are the real Phase 4 regression guards — they fail if Phase 4 is removed.
///
/// This test's value is as a sanity check that the verification pipeline
/// does not vacuously accept all postconditions.
///
/// Re: #759 — Phase 4 borrow resolution for unchanged mutable reference parameters
#[test]
#[timeout(30000)]
fn verify_postcondition_unchanged_mut_ref_bool_borrow_resolution_contradicts() {
    let invariants = vec![PureExpr::Bool(true)];
    let loop_condition = PureExpr::Var("flag".to_string(), None);
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "y".to_string(),
            Some(ExprSort::Bool),
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Bool(true)),
    )];
    // Postcondition: ^y == false — contradicts *y == true with y unchanged.
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "y".to_string(),
            Some(ExprSort::Bool),
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Bool(false)),
    )];
    let modified_vars: Vec<&str> = Vec::new();
    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };

    let result = verify_postcondition(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &requires, &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("postcondition encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "^y == false should FAIL when *y == true and y is unchanged. Got {result:?}. \
         If Verified, the pipeline is vacuously accepting postconditions."
    );
}

/// CARDINAL SOUNDNESS GUARD (prophecy false-accept sentinel).
///
/// A `&mut` loop variable that is MODIFIED by the loop body (reassigned and/or
/// mutated through its deref — the `all_zero_list::loop_l = next` / `*value = 0`
/// shape) must NOT have its prophecy collapsed to its current value. For a
/// mutated `&mut T`, `^x` (the prophecy/final value) genuinely differs from `*x`
/// (the current value), so asserting `x_final == x_current` would be the
/// catastrophic prophecy false-accept the campaign guards against
/// (bug/459, bug/1565, bug/1966 sentinels; #1823 deferral).
///
/// `final == current` is sound ONLY for SHARED (`&T`) borrows — but a `&T` loop
/// variable can never carry a `^x`/`_final` obligation, because the prophecy
/// operator is not well-typed on a shared reference. So a corpus shared-reborrow
/// loop (e.g. `binary_search_list::index`'s `l = &*ls`) never reaches this path.
/// The ONLY loop variables that have a `_final` are `&mut`, and a MODIFIED one
/// must stay UNRESOLVED. This test pins that boundary: it must NOT Verify (the
/// negated `^x == 42` is satisfiable because `x_final` is left free), and a
/// regression that emits `final == current` for a modified `&mut` would wrongly
/// Verify it.
///
/// Mirrors `all_zero_list`'s Obligation 2: `loop_l` is `MutRef(Datatype)` and is
/// in `modified_vars` (`["next", "loop_l", "value"]`), so postcondition.rs's
/// borrow-resolution block (the `modified_set.contains` guard at ~line 449)
/// correctly skips it. Closing that obligation soundly requires the inductive
/// length-preservation lemma, NOT a prophecy axiom.
#[test]
#[timeout(30000)]
fn modified_mut_ref_loop_var_prophecy_is_not_collapsed_to_current() {
    // Scenario mirrors `all_zero_list`'s loop_l: a `&mut i32` whose pointee is
    // mutated by the loop body (`*x = *x + 1`), so x is in modified_vars via the
    // deref body effect. Precondition `*x == 42`. Postcondition `^x == 42`.
    //
    // Because x is mutated, its prophecy ^x is NOT equal to the current *x at
    // loop exit — x_final must stay free, so the negated postcondition is SAT
    // and the result is NOT Verified. If a future change unsoundly collapses
    // `x_final == x_current` for this modified &mut, this assert flips and the
    // prophecy false-accept has been (re)introduced.
    let invariants = vec![PureExpr::Bool(true)];
    let loop_condition = PureExpr::Var("flag".to_string(), None);
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    )];
    // Postcondition: ^x == 42 — must NOT be provable for a mutated &mut.
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    )];
    // x IS modified: the loop body writes through its deref (`*x = *x + 1`).
    let modified_vars: Vec<&str> = vec!["x"];
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert(
        "x".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );
    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };

    let result = verify_postcondition(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &requires, &[]),
        effects(&HashMap::new(), &deref_body_effect, &HashMap::new()),
        &config,
    )
    .expect("postcondition encoding should succeed");

    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "PROPHECY FALSE-ACCEPT: ^x == 42 must NOT be Verified for a MODIFIED &mut \
         loop variable (x_final must stay free). Got {result:?}. A Verified result \
         means `x_final == x_current` was unsoundly emitted for a mutated &mut — \
         the catastrophic prophecy false-accept (cf. all_zero_list::loop_l, \
         bug/459+1565+1966)."
    );
}

/// Phase 4 borrow resolution with Int-sorted unchanged mutable reference.
/// When `*x == 42` is a require and `x` is not modified, `^x == 42` must verify.
/// This covers the non-Bool path in Phase 4 (postcondition.rs:351-354) where
/// `resolve_var_sort_or_int` determines the sort for the equality constraint.
///
/// Re: #759 — Phase 4 borrow resolution for unchanged mutable reference parameters
#[test]
#[timeout(30000)]
fn verify_postcondition_unchanged_mut_ref_int_borrow_resolves() {
    let invariants = vec![PureExpr::Bool(true)];
    let loop_condition = PureExpr::Var("flag".to_string(), None);
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    )];
    let modified_vars: Vec<&str> = Vec::new();
    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };

    let result = verify_postcondition(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &requires, &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("postcondition encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Phase 4 borrow resolution should prove ^x == 42 for unchanged &mut i32. \
         Got {result:?}. If Failed, the Int-sorted path in Phase 4 is broken."
    );
}
