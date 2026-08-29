// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::BTreeMap, sync::Arc};

use trust_wp_ay::{verify_loop_invariant, BodyEffects, LoopEncoderConfig, LoopVerificationContext};
use trust_wp_core::formula::NamedBindingValue;

use super::{
    expr_referenced_vars, infer_parameter_frame_invariants, rewrite_loop_postcondition_old,
    stable_type_invariants::{deref_changed, make_changed_places},
    BinOp, ChangedPlaces, PureExpr, VerificationResult,
};

/// #2158 regression: frame constraint filtering must check value expressions.
///
/// Scenario: `let n = v.len()` before a loop that modifies `v`. The variable
/// `n` is NOT in `modified_vars`, but its value expression `v.len()` references
/// `v`, which IS modified. A frame constraint `n == v.len()` would be unsound
/// because it asserts `n` equals the *current* (post-loop) value of `v.len()`,
/// not the pre-loop snapshot.
///
/// The CORRECT filter (used by `infer_stable_loop_invariants`) checks both:
/// 1. Whether the variable name is in `modified_vars`
/// 2. Whether the value expression references any variable in `modified_vars`
///
/// The BUGGY filter (in `verify_contract_loop_path`) only checks (1).
/// This test documents the correct behavior so a fix can be verified.
#[test]
fn frame_constraint_value_expr_must_check_modified_vars() {
    use std::collections::HashSet;

    // Setup: pre_loop_assignments = { "n" -> v.len(), "c" -> Int(42) }
    // modified_vars = ["v"]
    let pre_loop_assignments = BTreeMap::from([
        (
            "n".to_string(),
            PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("v".to_string(), None),
                ))))),
                method: "len".to_string(),
                args: vec![],
            },
        ),
        ("c".to_string(), PureExpr::Int(42)),
    ]);
    let modified_vars: Vec<String> = vec!["v".to_string()];
    let modified_set: HashSet<&str> = modified_vars.iter().map(String::as_str).collect();

    // CORRECT filter: check both name and value-expression variables.
    let correct_frame: Vec<&str> = pre_loop_assignments
        .iter()
        .filter(|(name, value)| {
            if modified_set.contains(name.as_str()) {
                return false;
            }
            let value_vars = expr_referenced_vars(value);
            !value_vars.iter().any(|v| modified_set.contains(v.as_str()))
        })
        .map(|(name, _)| name.as_str())
        .collect();

    // Only "c" should survive — "n"'s value references modified "v".
    assert_eq!(
        correct_frame,
        vec!["c"],
        "correct filter should exclude 'n' because its value references modified 'v'"
    );

    // BUGGY filter (current code in verify_contract_loop_path): only checks name.
    let buggy_frame: Vec<&str> = pre_loop_assignments
        .iter()
        .filter(|(name, _)| !modified_set.contains(name.as_str()))
        .map(|(name, _)| name.as_str())
        .collect();

    // This assertion documents the bug: the buggy filter incorrectly keeps "n".
    assert_eq!(
        buggy_frame,
        vec!["c", "n"],
        "buggy filter keeps 'n' because it only checks name, not value expression"
    );

    // Verify that expr_referenced_vars correctly identifies "v" in n's value.
    let n_value = &pre_loop_assignments["n"];
    let n_refs = expr_referenced_vars(n_value);
    assert!(
        n_refs.contains("v"),
        "expr_referenced_vars should find 'v' in v.len() expression: {n_refs:?}"
    );
}

// ── old() rewrite tests (#2095) ─────────────────────────────────────────

#[test]
fn rewrite_old_stable_param_strips_old() {
    // old(n) where n is a stable parameter → should become just n.
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
            "n".to_string(),
            None,
        )))),
    )];
    let arg_names = vec!["n".to_string()];
    let mut_ref_params = std::collections::HashSet::new();
    let pre_loop_written = std::collections::HashSet::new();
    let modified = vec!["i".to_string()];

    let result = rewrite_loop_postcondition_old(
        &ensures,
        &arg_names,
        &mut_ref_params,
        &pre_loop_written,
        &modified,
    )
    .expect("stable param should succeed");
    assert_eq!(result.len(), 1);
    // Old(Var("n")) should become Var("n")
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    assert_eq!(
        result[0], expected,
        "Old(n) should be stripped for stable param"
    );
}

#[test]
fn rewrite_old_stable_param_expr_strips_old() {
    // old(n + 1) where n is a stable parameter → should become n + 1.
    let ensures = vec![PureExpr::Old(Arc::new(PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    )))];
    let arg_names = vec!["n".to_string()];
    let mut_ref_params = std::collections::HashSet::new();
    let pre_loop_written = std::collections::HashSet::new();
    let modified = vec!["i".to_string()];

    let result = rewrite_loop_postcondition_old(
        &ensures,
        &arg_names,
        &mut_ref_params,
        &pre_loop_written,
        &modified,
    )
    .expect("stable param expr should succeed");
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    assert_eq!(result[0], expected, "Old(n + 1) should become n + 1");
}

#[test]
fn rewrite_old_modified_var_is_rejected() {
    // old(i) where i is modified by the loop → should be rejected.
    let ensures = vec![PureExpr::Old(Arc::new(PureExpr::Var(
        "i".to_string(),
        None,
    )))];
    let arg_names = vec!["i".to_string()];
    let mut_ref_params = std::collections::HashSet::new();
    let pre_loop_written = std::collections::HashSet::new();
    let modified = vec!["i".to_string()];

    let err = rewrite_loop_postcondition_old(
        &ensures,
        &arg_names,
        &mut_ref_params,
        &pre_loop_written,
        &modified,
    )
    .expect_err("modified var should be rejected");
    let msg = format!("{err}");
    assert!(
        msg.contains("modified by the loop body"),
        "error should mention loop modification: {msg}"
    );
}

#[test]
fn rewrite_old_pre_loop_written_param_is_rejected() {
    // old(x) where x is reassigned before the loop → should be rejected.
    let ensures = vec![PureExpr::Old(Arc::new(PureExpr::Var(
        "x".to_string(),
        None,
    )))];
    let arg_names = vec!["x".to_string()];
    let mut_ref_params = std::collections::HashSet::new();
    let pre_loop_written = std::collections::HashSet::from(["x".to_string()]);
    let modified = vec![];

    let err = rewrite_loop_postcondition_old(
        &ensures,
        &arg_names,
        &mut_ref_params,
        &pre_loop_written,
        &modified,
    )
    .expect_err("pre-loop written param should be rejected");
    let msg = format!("{err}");
    assert!(
        msg.contains("reassigned before loop entry"),
        "error should mention pre-loop reassignment: {msg}"
    );
}

#[test]
fn rewrite_old_deref_mut_borrow_is_preserved() {
    // old(*x) where x is a &mut parameter → Old(Deref(Var("x"))) should be preserved.
    let ensures = vec![PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
        PureExpr::Var("x".to_string(), None),
    ))))];
    let arg_names = vec!["x".to_string()];
    let mut_ref_params = std::collections::HashSet::from(["x".to_string()]);
    let pre_loop_written = std::collections::HashSet::new();
    let modified = vec!["x".to_string()];

    let result = rewrite_loop_postcondition_old(
        &ensures,
        &arg_names,
        &mut_ref_params,
        &pre_loop_written,
        &modified,
    )
    .expect("Old(Deref) for mut ref should be preserved");
    assert_eq!(
        result[0], ensures[0],
        "Old(Deref(Var(x))) should be preserved for &mut params"
    );
}

#[test]
fn rewrite_old_non_param_local_is_rejected() {
    // old(local_var) where local_var is not a function parameter → should be rejected.
    let ensures = vec![PureExpr::Old(Arc::new(PureExpr::Var(
        "local_var".to_string(),
        None,
    )))];
    let arg_names = vec!["n".to_string()];
    let mut_ref_params = std::collections::HashSet::new();
    let pre_loop_written = std::collections::HashSet::new();
    let modified = vec![];

    let err = rewrite_loop_postcondition_old(
        &ensures,
        &arg_names,
        &mut_ref_params,
        &pre_loop_written,
        &modified,
    )
    .expect_err("non-param local should be rejected");
    let msg = format!("{err}");
    assert!(
        msg.contains("not a function parameter"),
        "error should mention non-parameter: {msg}"
    );
}

// --- infer_parameter_frame_invariants tests (#1816 Phase 2) ---

#[test]
fn prophecy_frame_basic() {
    // &mut param "x" unchanged → produces 1 prophecy frame invariant + 1 pre-loop assignment
    let arg_names = vec!["x".to_string()];
    let mut mut_refs = std::collections::HashSet::new();
    mut_refs.insert("x".to_string());
    let changed = make_changed_places(&["i"]); // only "i" modified, not "x"
    let pre_loop = std::collections::HashMap::new();

    let (assignments, invariants) = infer_parameter_frame_invariants(
        &arg_names,
        &mut_refs,
        &changed,
        &pre_loop,
        &[],
        &vec!["i".to_string()],
    );

    assert_eq!(
        invariants.len(),
        1,
        "should infer 1 prophecy frame invariant"
    );
    assert_eq!(
        assignments.len(),
        1,
        "should add 1 synthetic pre-loop assignment"
    );
    assert!(
        assignments.contains_key("x_final_old"),
        "pre-loop assignment should be for x_final_old"
    );
    // The invariant should be: Final(Var("x")) == Var("x_final_old")
    let expected_inv = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Var("x_final_old".to_string(), None)),
    );
    assert_eq!(invariants[0], expected_inv);
}

#[test]
fn prophecy_frame_modified_pointee() {
    // &mut param "x" where *x is modified → no prophecy frame
    let arg_names = vec!["x".to_string()];
    let mut mut_refs = std::collections::HashSet::new();
    mut_refs.insert("x".to_string());
    // "x" has Deref(Changed) → pointee modified
    let mut map = std::collections::HashMap::new();
    map.insert("x".to_string(), deref_changed());
    let changed = ChangedPlaces(map);
    let pre_loop = std::collections::HashMap::new();

    let (assignments, invariants) = infer_parameter_frame_invariants(
        &arg_names,
        &mut_refs,
        &changed,
        &pre_loop,
        &[],
        &vec!["i".to_string()],
    );

    assert!(
        invariants.is_empty(),
        "should not infer prophecy frame when pointee is modified"
    );
    assert!(assignments.is_empty());
}

#[test]
fn prophecy_frame_non_mut() {
    // Non-&mut param "n" unchanged → no prophecy frame (only &mut gets prophecy)
    let arg_names = vec!["n".to_string()];
    let mut_refs = std::collections::HashSet::new(); // "n" is NOT &mut
    let changed = ChangedPlaces::default();
    let pre_loop = std::collections::HashMap::new();

    let (assignments, invariants) = infer_parameter_frame_invariants(
        &arg_names,
        &mut_refs,
        &changed,
        &pre_loop,
        &[],
        &vec!["i".to_string()],
    );

    assert!(
        invariants.is_empty(),
        "non-&mut param should not get prophecy frame"
    );
    assert!(assignments.is_empty());
}

#[test]
fn prophecy_frame_empty_modified_vars_skipped() {
    // bug/1743 shape: &mut self with no body modifications.
    // When modified_vars is empty, the loop encoder never primes any
    // variable, so the synthetic `^self == self_final_old` invariant is
    // vacuous AND adds an untyped binding that triggers spurious sort
    // coercion against ^self's MutRef-derived sort (#5226).
    let arg_names = vec!["self".to_string()];
    let mut mut_refs = std::collections::HashSet::new();
    mut_refs.insert("self".to_string());
    let changed = ChangedPlaces::default(); // No changes anywhere.
    let pre_loop = std::collections::HashMap::new();

    let (assignments, invariants) = infer_parameter_frame_invariants(
        &arg_names,
        &mut_refs,
        &changed,
        &pre_loop,
        &[],
        &[], // empty modified_vars → inference should bail
    );
    assert!(
        invariants.is_empty(),
        "prophecy frame inv should be skipped when modified_vars is empty: {invariants:?}"
    );
    assert!(
        assignments.is_empty(),
        "no synthetic pre-loop assignment should be emitted: {assignments:?}"
    );
}

#[test]
fn prophecy_frame_dedup() {
    // User already wrote ^x == x_final_old → should not duplicate
    let arg_names = vec!["x".to_string()];
    let mut mut_refs = std::collections::HashSet::new();
    mut_refs.insert("x".to_string());
    let changed = ChangedPlaces::default(); // x unchanged
    let pre_loop = std::collections::HashMap::new();

    let existing_inv = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Var("x_final_old".to_string(), None)),
    );

    let (assignments, invariants) = infer_parameter_frame_invariants(
        &arg_names,
        &mut_refs,
        &changed,
        &pre_loop,
        &[existing_inv],
        &["i".to_string()],
    );

    assert!(
        invariants.is_empty(),
        "should skip when invariant already exists"
    );
    assert!(assignments.is_empty());
}

#[test]
fn prophecy_frame_integrates_with_loop_verifier() {
    // Direct Phase 2 -> trust-wp-ay integration check: the synthesized
    // `x_final_old = ^x` binding must initialize and preserve the inferred
    // invariant `^x == x_final_old` through loop verification.
    let arg_names = vec!["x".to_string()];
    let mut mut_refs = std::collections::HashSet::new();
    mut_refs.insert("x".to_string());
    let changed = make_changed_places(&["i"]);

    let mut pre_loop = std::collections::HashMap::new();
    pre_loop.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let (synthetic_assignments, invariants) = infer_parameter_frame_invariants(
        &arg_names,
        &mut_refs,
        &changed,
        &pre_loop,
        &[],
        &vec!["i".to_string()],
    );
    pre_loop.extend(synthetic_assignments);

    assert_eq!(
        invariants.len(),
        1,
        "expected one synthesized prophecy frame invariant"
    );

    let ensures = invariants.clone();
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Int(3)),
    );
    let mut body_effect = std::collections::HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );
    let config = LoopEncoderConfig::default().with_timeout(std::time::Duration::from_secs(5));
    let empty_deref_effects = std::collections::HashMap::new();
    let empty_double_deref_effects = std::collections::HashMap::new();
    let result = verify_loop_invariant(
        &LoopVerificationContext::new(
            &[],
            &ensures,
            &invariants,
            &["i"],
            BodyEffects::new(
                &body_effect,
                &empty_deref_effects,
                &empty_double_deref_effects,
            ),
            &pre_loop,
        )
        .with_loop_condition(&loop_condition)
        .with_config(config),
    )
    .expect("phase-2 prophecy frame facts should encode through loop verification");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "prophecy frame initialization should verify, got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "prophecy frame preservation should verify, got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "prophecy frame postcondition should verify, got {:?}",
        result.postcondition
    );
}

// --- modified-parameter initial-value substitution tests (#2665) ---

/// #2665 regression: modified by-value parameter → snapshot deref rewrite.
///
/// Models the Creusot `variant_int` pattern:
///   #[ensures(result == x)]
///   pub fn variant_int(mut x: u32) -> u32 {
///     let mut result = 0;
///     let total = snapshot!(x@);
///     #[variant(x)]
///     #[invariant(*total == x@ + result@)]
///     while x > 0 { x -= 1; result += 1 }
///     result
///   }
///
/// In Creusot semantics, `ensures(result == x)` refers to the initial value
/// of `x`. The driver finds the snapshot binding `total → View(Var("x"))`
/// in pre_loop_assignments and rewrites ensures to `result == *total`
/// (i.e., `result == Deref(Var("total"))`).
///
/// This test validates the ay-level behavior: with the snapshot-dereferenced
/// ensures `result == *total`, the user-written invariant `*total == x + result`
/// proves the postcondition at loop exit (x==0 → *total == result).
#[test]
fn modified_param_snapshot_deref_variant_int_pattern() {
    use std::time::Duration;

    // invariant: *total == x + result (after scalar view stripping)
    let invariant = PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "total".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "result".to_string(),
                None,
            )))),
        )),
    );
    let invariants = vec![invariant];

    // requires: x >= 0 (unsigned bound)
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];

    // ensures: result == *total (after driver snapshot deref rewrite #2665)
    // The driver found `total → View(Var("x"))` and rewrote `x` → `Deref(total)`.
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "total".to_string(),
            None,
        )))),
    )];
    let return_expr = PureExpr::Var("result".to_string(), None);

    let modified_vars: Vec<&str> = vec!["x", "result"];
    let mut body_effect = std::collections::HashMap::new();
    body_effect.insert(
        "x".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Sub,
            Arc::new(PureExpr::Int(1)),
        ),
    );
    body_effect.insert(
        "result".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let mut pre_loop = std::collections::HashMap::new();
    pre_loop.insert(
        "result".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    pre_loop.insert(
        "total".to_string(),
        NamedBindingValue::untyped(PureExpr::View(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
    );

    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let variant_expr = PureExpr::Var("x".to_string(), None);
    let empty_deref = std::collections::HashMap::new();
    let empty_double_deref = std::collections::HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_variant(&variant_expr)
    .with_config(LoopEncoderConfig::default().with_timeout(Duration::from_secs(15)));

    let result =
        verify_loop_invariant(&ctx).expect("variant_int pattern with snapshot deref should encode");

    // Initialization: total = View(x), result = 0
    // Invariant: Deref(total) == View(x) + View(result)
    // After deref-through + scalar strip: x == x + 0 → trivially true
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify: x == x + 0 after deref-through; got {:?}",
        result.initialization
    );

    // Preservation: invariant preserved since (x-1) + (result+1) = x + result
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify: (x-1)+(result+1) = x+result; got {:?}",
        result.preservation
    );

    // Postcondition: at exit x==0, invariant gives *total == 0 + result,
    // so *total == result, and ensures result == *total holds.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition with snapshot deref should verify; got {:?}",
        result.postcondition
    );

    // Variant checks
    assert!(
        result.variant_nonneg.is_some(),
        "variant nonneg should be checked"
    );
    assert!(
        matches!(
            result.variant_nonneg.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant nonneg should verify; got {:?}",
        result.variant_nonneg
    );
    assert!(
        result.variant_decrease.is_some(),
        "variant decrease should be checked"
    );
    assert!(
        matches!(
            result.variant_decrease.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant decrease should verify; got {:?}",
        result.variant_decrease
    );
}

/// #2665: ensures without modified params should NOT be rewritten.
///
/// Models a loop where the postcondition references only unmodified
/// parameters — no substitution needed.
#[test]
fn unmodified_param_ensures_not_rewritten() {
    // This is a pure structural test: verify that the substitution
    // logic doesn't touch parameters not in modified_vars.
    use std::collections::HashSet;

    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    )];
    let arg_names = vec!["n".to_string()];
    let modified_vars: Vec<String> = vec!["i".to_string()]; // n is NOT modified

    let modified_set: HashSet<&str> = modified_vars.iter().map(String::as_str).collect();
    let mut_ref_params: HashSet<String> = HashSet::new();

    // Check: n should NOT be substituted because it's not modified.
    let param_in_ensures_and_modified = arg_names.iter().any(|p| {
        modified_set.contains(p.as_str())
            && !mut_ref_params.contains(p)
            && ensures
                .iter()
                .any(|e| expr_referenced_vars(e).iter().any(|v| v == p))
    });

    assert!(
        !param_in_ensures_and_modified,
        "unmodified param 'n' should not trigger substitution"
    );
}
