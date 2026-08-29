// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use super::*;

// Auto-frame invariant edge cases (#1816)
// -----------------------------------------------------------------------

/// Auto-frame invariant: an unmodified variable with a constant pre-loop value
/// gets `var == constant` as an auto-invariant, enabling postcondition proofs.
///
/// Models:
///   let limit = 10;
///   let mut i = 0;
///   while i < limit { i += 1 }
///   ensures: result == 10
///
/// Without the auto-frame invariant for `limit`, the postcondition cannot
/// derive `result == 10` because `limit` is an unconstrained free variable
/// after the loop. The auto-invariant `limit == 10` bridges the gap.
#[test]
#[timeout(30000)]
fn auto_frame_invariant_unmodified_constant_enables_postcondition() {
    let requires: Vec<PureExpr> = vec![];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("limit"))];
    let ensures = vec![eq(var("result"), int(10))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert("limit".to_string(), NamedBindingValue::untyped(int(10)));
    let loop_condition = lt(var("i"), var("limit"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("auto-frame constant should encode");

    // The auto-frame invariant `limit == 10` should make all VCs provable.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: auto-frame gives limit==10, i=0, so 0<=0<=10; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: 0<=i<=limit, limit==10, i<limit => 0<=i+1<=limit; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i<=limit, limit==10, NOT(i<limit) => i==10; got {:?}",
        result.postcondition
    );
}

/// Auto-frame invariant MUST NOT be generated for a variable whose pre-loop
/// value references a modified variable.
///
/// Models:
///   let mut i = 0;
///   let snapshot_i = i;  // pre-loop value references `i`, which is modified
///   while i < n { i += 1 }
///   ensures: result == n
///
/// If `snapshot_i == i` were asserted as a frame invariant, it would be
/// FALSE after the first iteration (i changes but snapshot_i doesn't).
/// The filter at mod.rs:249 (`expr_references_any_var`) must exclude this.
///
/// We verify that the pipeline still works (the user-provided invariants
/// are sufficient), and that it does NOT accidentally constrain `snapshot_i`.
#[test]
#[timeout(30000)]
fn auto_frame_invariant_skips_var_referencing_modified() {
    let requires = vec![ge(var("n"), int(0))];
    // User invariants are sufficient on their own.
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // snapshot_i's pre-loop value is `var("i")` — references modified var `i`.
    // This MUST NOT generate `snapshot_i == i` as an auto-frame invariant.
    pre_loop_assignments.insert(
        "snapshot_i".to_string(),
        NamedBindingValue::untyped(var("i")),
    );

    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result =
        verify_loop_invariant(&ctx).expect("modified-var-reference filter should not error");

    // All VCs should still verify — the user invariants are self-contained.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify with user invariants alone; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify with user invariants alone; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify with user invariants alone; got {:?}",
        result.postcondition
    );
}

/// Auto-frame invariant with Seq-sorted variable: ensures that variables
/// annotated with `ExprSort::Seq` in pre-loop assignments get correct
/// auto-frame invariants that the encoder can handle.
///
/// Models:
///   let items: Seq<i32> = ...; // Seq-sorted, not modified
///   let mut i = 0;
///   while i < n { i += 1 }
///   ensures: result == n
///
/// The Seq-sorted variable `items` gets an auto-frame invariant
/// `items == items_initial_value`. The encoder must handle this without
/// sort mismatches (Seq == Seq, not Seq == Int).
#[test]
#[timeout(30000)]
fn auto_frame_invariant_seq_sorted_variable() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // Seq-sorted variable with a method call as initial value (e.g., `v.deep_model()`).
    // Using a Var with Seq sort annotation to exercise sort-aware auto-frame.
    pre_loop_assignments.insert(
        "items".to_string(),
        NamedBindingValue::new(Some(ExprSort::Seq), var_with_sort("v_model", ExprSort::Seq)),
    );

    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("Seq-sorted auto-frame should encode");

    // All VCs should verify — the Seq variable is unmodified and its
    // auto-frame invariant doesn't interfere with the Int-sorted proof.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init with Seq auto-frame should verify; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation with Seq auto-frame should verify; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition with Seq auto-frame should verify; got {:?}",
        result.postcondition
    );
}

/// Auto-frame invariant with FMap-sorted variable: ensures FMap-sorted
/// pre-loop assignments generate auto-frame invariants without sort errors.
///
/// Models:
///   let map: FMap<K, V> = ...; // FMap-sorted, not modified
///   let mut i = 0;
///   while i < n { i += 1 }
///   ensures: result == n
#[test]
#[timeout(30000)]
fn auto_frame_invariant_fmap_sorted_variable() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // FMap-sorted variable, not modified by the loop.
    pre_loop_assignments.insert(
        "map".to_string(),
        NamedBindingValue::new(
            Some(ExprSort::FMap),
            var_with_sort("original_map", ExprSort::FMap),
        ),
    );

    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("FMap-sorted auto-frame should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init with FMap auto-frame should verify; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation with FMap auto-frame should verify; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition with FMap auto-frame should verify; got {:?}",
        result.postcondition
    );
}

/// Auto-frame invariant combined with type invariant: the type invariant
/// axiom for an unmodified variable remains provable because auto-frame
/// preserves the variable's value across iterations.
///
/// Models:
///   // #[invariant(self.value >= 0)]
///   // struct Counter { value: i32 }
///   let counter = Counter { value: 5 };  // not modified
///   let mut i = 0;
///   while i < n { i += 1 }
///   ensures: result == n
///
/// The type invariant axiom `inv_Counter(counter) => counter.value >= 0`
/// is registered as a solver axiom. The auto-frame invariant `counter == 5`
/// pins the variable value, ensuring the type invariant holds throughout.
/// This test exercises the interaction between auto-frame and type invariant
/// axioms in the loop encoder.
#[test]
#[timeout(30000)]
fn auto_frame_invariant_with_type_invariant_axiom() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // Unmodified variable representing a typed value.
    pre_loop_assignments.insert("counter".to_string(), NamedBindingValue::untyped(int(5)));

    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    // Register a type invariant: inv_Counter(self) => self >= 0.
    // For simplicity in this test, `counter` is Int-sorted and the invariant
    // body uses the self parameter directly. In production, this would be a
    // Datatype sort with field selectors.
    let type_inv = trust_wp_core::type_invariant_def! {
        type_name: "Counter".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ge(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    };
    let type_invs = vec![type_inv];

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(
        LoopEncoderConfig {
            timeout: Some(Duration::from_secs(10)),
            ..LoopEncoderConfig::default()
        }
        .with_type_invariants(&type_invs),
    );

    let result =
        verify_loop_invariant(&ctx).expect("auto-frame with type invariant axiom should encode");

    // Auto-frame gives `counter == 5` as invariant. Combined with the type
    // invariant axiom `inv_Counter(counter) => counter >= 0`, the prover
    // knows counter >= 0 throughout. The main proof (i-counting) still works.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init with type invariant + auto-frame should verify; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation with type invariant + auto-frame should verify; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition with type invariant + auto-frame should verify; got {:?}",
        result.postcondition
    );
}

/// Auto-frame invariant for a variable whose pre-loop value is a complex
/// expression (not just a simple variable or constant) that does NOT
/// reference any modified variable.
///
/// Models:
///   let bound = a + b;  // complex expression, but a and b are unmodified
///   let mut i = 0;
///   while i < bound { i += 1 }
///   ensures: result == a + b
///
/// The auto-frame invariant `bound == a + b` should be generated because
/// neither `a` nor `b` is in modified_vars, even though the pre-loop value
/// is a non-trivial expression.
#[test]
#[timeout(30000)]
fn auto_frame_invariant_complex_unmodified_expression() {
    let requires = vec![ge(var("a"), int(0)), ge(var("b"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("bound"))];
    let ensures = vec![eq(var("result"), add(var("a"), var("b")))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // bound = a + b; neither a nor b is modified.
    pre_loop_assignments.insert(
        "bound".to_string(),
        NamedBindingValue::untyped(add(var("a"), var("b"))),
    );

    let loop_condition = lt(var("i"), var("bound"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("complex expression auto-frame should encode");

    // Auto-frame invariant `bound == a + b` combined with invariant `i <= bound`
    // and exit condition NOT(i < bound) gives `i == bound == a + b`.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init with complex auto-frame should verify; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation with complex auto-frame should verify; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: result == a+b via auto-frame bound==a+b; got {:?}",
        result.postcondition
    );
}

/// Auto-frame invariant: modified variable itself must NOT get auto-frame.
///
/// Verifies that a variable listed in `modified_vars` is correctly excluded
/// from auto-frame invariant generation, even though it has a pre-loop
/// assignment.
#[test]
#[timeout(30000)]
fn auto_frame_invariant_excludes_modified_variable() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("modified-var exclusion should encode");

    // If `i == 0` were incorrectly added as auto-frame invariant, preservation
    // would fail because i changes from 0 to i+1. The fact that all VCs verify
    // with the user-provided invariants proves the exclusion works correctly.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: user invariants sufficient; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: would fail if i==0 auto-frame leaked; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: user invariants sufficient; got {:?}",
        result.postcondition
    );
}

/// Auto-frame invariant skips variables whose sort is a Datatype but whose
/// pre-loop value is a bare Int literal.
///
/// This happens when lossy ADT translation (e.g., `Some(10)` lowered to
/// `Int(10)`) strips the constructor. The resulting `var == Int(N)` equality
/// would trigger sort coercion to a fresh unconstrained constant, making
/// preservation trivially fail. The filter at mod.rs:260-268 catches this.
///
/// Models:
///   let opt: Option<i32> = Some(10);  // lowered to Int(10) with Datatype sort
///   let mut i = 0;
///   while i < n { i += 1 }
///   ensures: result == n
///
/// Without the sort-mismatch filter, the auto-frame invariant `opt == 10`
/// would be generated with a Datatype-sorted LHS and Int-sorted RHS, causing
/// encoding errors or unsound proofs.
#[test]
#[timeout(30000)]
fn auto_frame_invariant_skips_int_literal_with_datatype_sort() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // Datatype-sorted variable with a bare Int literal value.
    // This mimics lossy ADT lowering: Some(10) -> Int(10) with Datatype sort.
    let option_sort_id = trust_wp_core::formula::intern_sort_name("Option");
    pre_loop_assignments.insert(
        "opt".to_string(),
        NamedBindingValue::new(Some(ExprSort::Datatype(option_sort_id)), int(10)),
    );

    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("sort-mismatch filter should not error");

    // All VCs should verify -- user invariants are sufficient, and the
    // potentially problematic `opt == 10` auto-frame invariant should be
    // filtered out by the sort-mismatch guard.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: user invariants sufficient; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: should not have sort-mismatched auto-frame; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: user invariants sufficient; got {:?}",
        result.postcondition
    );
}

/// Multiple unchanged variables all get auto-frame invariants, enabling a
/// postcondition that references several of them.
///
/// Models:
///   let a = 3;
///   let b = 7;
///   let mut i = a;
///   while i < b { i += 1 }
///   ensures: result == b  (i.e., result == 7)
///
/// Both `a` and `b` are unmodified. Auto-frame generates `a == 3` and
/// `b == 7`. Combined with user invariant `i <= b` and exit condition
/// NOT(i < b), the postcondition `result == b` is provable.
#[test]
#[timeout(30000)]
fn auto_frame_invariant_multiple_unchanged_vars() {
    let requires: Vec<PureExpr> = vec![];
    let invariants = vec![ge(var("i"), var("a")), le(var("i"), var("b"))];
    let ensures = vec![eq(var("result"), var("b"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("a")));
    pre_loop_assignments.insert("a".to_string(), NamedBindingValue::untyped(int(3)));
    pre_loop_assignments.insert("b".to_string(), NamedBindingValue::untyped(int(7)));

    let loop_condition = lt(var("i"), var("b"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("multi-unchanged-vars should encode");

    // Auto-frame gives a==3, b==7. Init: i=a=3, a<=3<=7=b. Preservation:
    // a<=i<=b, i<b => a<=i+1<=b. Post: i<=b, NOT(i<b) => i==b.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init with multiple auto-frames should verify; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation with multiple auto-frames should verify; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: result==b via auto-frame b==7 and exit i==b; got {:?}",
        result.postcondition
    );
}

/// Auto-frame invariant for snapshot variable through the full pipeline.
///
/// Models the common Creusot snapshot pattern:
///   let old_val = snapshot!(x);  // pre-loop: old_val = x
///   let mut i = 0;
///   while i < n {
///     #[invariant(i >= 0 && i <= n)]
///     i += 1;
///   }
///   ensures: old_val == x  // x is unchanged
///
/// The auto-frame invariant `old_val == x` (from pre-loop assignment) plus
/// the auto-stable-requires (x not modified) enables the postcondition.
#[test]
#[timeout(30000)]
fn auto_frame_snapshot_full_pipeline() {
    let requires = vec![ge(var("n"), int(0)), gt(var("x"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("old_val"), var("x"))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // old_val = x (snapshot). Neither old_val nor x is modified.
    pre_loop_assignments.insert("old_val".to_string(), NamedBindingValue::untyped(var("x")));

    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("snapshot full pipeline should encode");

    // Auto-frame generates `old_val == x`. Since x is unmodified, this is
    // trivially preserved. The postcondition `old_val == x` is directly
    // an auto-frame invariant.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: auto-frame old_val==x holds at entry; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: old_val unmodified, x unmodified, so old_val==x preserved; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: old_val==x directly from auto-frame invariant; got {:?}",
        result.postcondition
    );
}

/// Combined test: auto-frame + auto-type-invariant + auto-stable-requires
/// all contribute to proving a postcondition.
///
/// Models:
///   #[invariant(self.0 > 0)]
///   struct NonZero(i32);
///
///   #[requires(x.invariant())]
///   #[requires(bound > 0)]
///   fn combined(x: NonZero, bound: i32) -> i32 {
///     let limit = bound;  // pre-loop assignment, unmodified
///     let mut i = 0;
///     while i < limit {
///       #[invariant(i >= 0)]
///       i += 1;
///     }
///     x.0  // unchanged, requires x.invariant() => x > 0
///   }
///   ensures: result > 0
///
/// This requires all three auto-invariant mechanisms:
///   - Auto-frame: `limit == bound` (enables i == limit at exit)
///   - Auto-type-invariant: `x.invariant()` (enables result > 0)
///   - Auto-stable-requires: `bound > 0` (enables limit > 0 via auto-frame)
#[test]
#[timeout(30000)]
fn combined_auto_frame_type_invariant_stable_requires() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");
    let inv_defs = [trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    }];

    // requires: x.invariant(), bound > 0
    let requires: Vec<PureExpr> = vec![
        method_call(var("x"), &inv_method, vec![]),
        gt(var("bound"), int(0)),
    ];

    // User invariant: i >= 0 (weak -- auto-invariants fill the gap)
    let invariants = vec![ge(var("i"), int(0))];

    // ensures: result > 0
    let ensures = vec![gt(var("result"), int(0))];
    let return_expr = var("x");

    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // limit = bound (auto-frame: limit == bound, since neither is modified)
    pre_loop_assignments.insert(
        "limit".to_string(),
        NamedBindingValue::untyped(var("bound")),
    );

    let loop_condition = lt(var("i"), var("limit"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let config = LoopEncoderConfig::default()
        .with_type_invariants(&inv_defs)
        .with_timeout(Duration::from_secs(10));

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(config);

    let result = verify_loop_invariant(&ctx).expect("combined auto-invariants should encode");

    // Postcondition: result > 0
    // Proof chain:
    //   1. Auto-type-invariant: x.invariant() => x > 0
    //   2. return_expr = x, so result == x
    //   3. Therefore result > 0
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify with combined auto-invariants; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify with combined auto-invariants; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: result > 0 from type invariant + auto-frame + stable requires; got {:?}",
        result.postcondition
    );
}
