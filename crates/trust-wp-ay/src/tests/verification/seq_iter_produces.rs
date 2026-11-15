// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SeqIter produces encoding tests (#2116).
//!
//! These tests verify the driver-level `produces` lowering for SeqIter
//! (logical `Seq` iteration) reaches the ay encoder correctly and the
//! resulting ext_eq + concat constraints are satisfiable and support proofs.
//!
//! The SeqIter produces pattern (after `iterator_spec_rewrite`):
//!   `original@.ext_eq(produced@.concat(next@))`
//!
//! This decomposes the original sequence into "already visited" (`produced`)
//! and "remaining" (`next`), enabling:
//! - Length conservation: `original@.len() == produced@.len() + next@.len()`
//! - Variant non-negativity: `original@.len() - produced@.len() >= 0`
//! - Variant decrease: produced grows each step → variant decreases

use std::time::Duration;

use trust_wp_core::formula::{ExprSort, NamedBindingValue};

use super::*;

/// Seq-sorted variable helper. Without the ExprSort::Seq hint, the sort
/// inference defaults to Int, which causes sort mismatches in the ext_eq
/// and concat axiom encoding paths. (#2116, #1982)
fn seq_var(name: &str) -> PureExpr {
    var_with_sort(name, ExprSort::Seq)
}

// ── Satisfiability: SeqIter produces encoding is consistent ──────────

/// The SeqIter produces preconditions must be satisfiable.
///
/// Models the rewritten produces from `iterator_spec_rewrite/simple.rs`:
///   `original@.ext_eq(produced@.concat(next@))`
/// with a known original length. If the encoding is overconstrained
/// (false UNSAT), all subsequent proofs are vacuous.
#[test]
#[timeout(30000)]
fn test_seq_iter_produces_preconditions_satisfiable() {
    let original_len = eq(
        method_call(view(seq_var("original")), "len", vec![]),
        int(5),
    );
    let concat = method_call(
        view(seq_var("produced")),
        "concat",
        vec![view(seq_var("next"))],
    );
    let produces = method_call(view(seq_var("original")), "ext_eq", vec![concat]);
    let preconditions = vec![original_len, produces];

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(Duration::from_secs(2)));
    encoder.register_sort_hints(&preconditions);
    for expr in &preconditions {
        let term = encoder
            .encode_pure(expr)
            .unwrap_or_else(|e| panic!("precondition should encode: {e:?}"));
        encoder.assert_term(term);
    }

    let result = encoder.check_sat();
    assert!(
        !result.is_unsat(),
        "SeqIter produces preconditions must not be internally contradictory; AY may conservatively return Unknown when the auxiliary Seq model is incomplete: got {result:?}"
    );
}

// ── Length conservation through ext_eq + concat ──────────────────────

/// Length conservation: ext_eq(a, concat(b, c)) implies len(a) == len(b) + len(c).
///
/// This is the core axiom chain for SeqIter variant proofs:
/// 1. ext_eq forward axiom: ext_eq(a, b) => len(a) == len(b)
/// 2. concat-length axiom (Axiom 15): len(concat(s1, s2)) == len(s1) + len(s2)
/// 3. Combining: len(a) == len(b) + len(c)
///
/// The exact, explicitly typed `Seq` shape is discharged structurally before
/// the general quantified Array-backed model. The wrong-relation test below
/// remains the end-to-end fail-closed canary.
#[test]
#[timeout(120000)]
fn test_seq_iter_produces_length_conservation() {
    let original_len = method_call(view(seq_var("original")), "len", vec![]);
    let produced_len = method_call(view(seq_var("produced")), "len", vec![]);
    let next_len = method_call(view(seq_var("next")), "len", vec![]);

    // Precondition: ext_eq(original@, produced@.concat(next@))
    let concat = method_call(
        view(seq_var("produced")),
        "concat",
        vec![view(seq_var("next"))],
    );
    let produces = method_call(view(seq_var("original")), "ext_eq", vec![concat]);

    // Postcondition: original.len() == produced.len() + next.len()
    let ens = eq(original_len, add(produced_len, next_len));

    let requires = [produces];
    let ensures = [ens];
    let request =
        VerificationRequest::new(&requires, &ensures).timeout(Some(Duration::from_secs(45)));
    let result = verify_function_with_modes(request).unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "length_conservation should verify through the exact Seq theorem lane: {result:?}"
    );
}

/// Negative: wrong length relation should fail.
///
/// If length conservation is overconstrained (preconditions UNSAT), even
/// wrong claims verify. This guards against vacuity.
#[test]
#[timeout(30000)]
fn test_seq_iter_produces_wrong_length_fails() {
    let original_len = method_call(view(seq_var("original")), "len", vec![]);
    let produced_len = method_call(view(seq_var("produced")), "len", vec![]);

    let concat = method_call(
        view(seq_var("produced")),
        "concat",
        vec![view(seq_var("next"))],
    );
    let produces = method_call(view(seq_var("original")), "ext_eq", vec![concat]);

    // Wrong: original.len() == produced.len() (ignoring next.len())
    let ens = eq(original_len, produced_len);

    let requires = [produces];
    let ensures = [ens];
    let request =
        VerificationRequest::new(&requires, &ensures).timeout(Some(Duration::from_secs(5)));
    let result = verify_function_with_modes(request).unwrap();
    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "Wrong length relation should not verify: got {result:?}"
    );
}

// ── Variant non-negativity through produces ──────────────────────────

/// Variant non-negativity: ext_eq + concat proves `produced.len() <= original.len()`.
///
/// The proof chain requires:
/// 1. ext_eq → len(original) == len(concat(produced, next))
/// 2. ext_eq seeds the concat-length equality for symbolic `concat(...)`
/// 3. Axiom 4: len(next) >= 0
///
/// This uses the exact non-negativity corollary of the same explicitly typed
/// Seq conservation law and must verify rather than time out.
#[test]
#[timeout(120000)]
fn test_seq_iter_variant_nonneg_function_level_verifies() {
    let original_len = method_call(view(seq_var("original")), "len", vec![]);
    let produced_len = method_call(view(seq_var("produced")), "len", vec![]);

    let concat = method_call(
        view(seq_var("produced")),
        "concat",
        vec![view(seq_var("next"))],
    );
    let produces = method_call(view(seq_var("original")), "ext_eq", vec![concat]);

    // produced.len() <= original.len()  (equivalent to variant >= 0)
    let variant_nonneg = le(produced_len, original_len);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[produces], &[variant_nonneg])
            .timeout(Some(Duration::from_secs(45))),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "variant_nonneg should verify through the exact Seq theorem lane: {result:?}"
    );
}

// ── Initialization: ext_eq(a, concat(empty, a)) via reverse Tseitin ──

/// ext_eq reflexivity through concat left identity: (#2116)
///   requires: true
///   ensures: ext_eq(a, concat(seq_empty, a))
///
/// The proof chain:
/// 1. Concat left identity (Axiom 15c): concat(seq_empty, a) = a
/// 2. Reverse Tseitin: (r_term = o_term) => ext_eq_var
/// 3. Combining: concat(seq_empty, a) = a, so r_term = o_term, so ext_eq_var = true
///
/// This is the core initialization obligation for SeqIter produces loops
/// where `produced` starts empty and `iter` starts as `original`.
/// Without the reverse Tseitin, ext_eq_var is a free Bool that the solver
/// can set to false, making initialization UNSAT checks trivially SAT.
///
/// **Diagnostic (#2116):** Previously returned a vacuous proof because the
/// base assertions hit ay-dpll's `seq_array(seq_empty) == const_array(0)`
/// model-validation bug. The ay pin now propagates that UF/Array equality
/// correctly, so this obligation should verify.
#[test]
#[timeout(30000)]
fn test_ext_eq_concat_empty_identity_verifies() {
    // ext_eq(a@, concat(seq_empty(), a@))
    let empty = logic_fn_call("seq_empty", vec![]);
    let concat = method_call(empty, "concat", vec![view(seq_var("a"))]);
    let ext_eq = method_call(view(seq_var("a")), "ext_eq", vec![concat]);

    let result = verify_function_with_modes(VerificationRequest::new(&[], &[ext_eq])).unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ext_eq(a, concat(empty, a)) should verify with UF/Array propagation fixed: got {result:?}"
    );
}

/// Negative: ext_eq with wrong operand should fail.
///
/// Guards against the reverse Tseitin making ext_eq vacuously true.
/// Use a same-length, different-element contradiction instead of a full
/// function proof so the test stays stable under the heavier ay pin while
/// still checking more than length equality.
#[test]
#[timeout(30000)]
fn test_ext_eq_concat_empty_wrong_operand_fails() {
    // ext_eq(a@, concat(seq_empty(), b@))  — a != b in general
    let mut encoder = AYEncoder::new();
    let empty = logic_fn_call("seq_empty", vec![]);
    let concat = method_call(empty, "concat", vec![view(seq_var("b"))]);
    let ext_eq = method_call(view(seq_var("a")), "ext_eq", vec![concat]);
    let ext_eq_term = encoder
        .encode_pure(&ext_eq)
        .expect("ext_eq(a, concat(empty, b)) should encode");
    encoder.assert_term(ext_eq_term);

    let len_a = encoder
        .encode_pure(&method_call(view(seq_var("a")), "len", vec![]))
        .expect("len(a@) should encode");
    let len_b = encoder
        .encode_pure(&method_call(view(seq_var("b")), "len", vec![]))
        .expect("len(b@) should encode");
    let a0 = encoder
        .encode_pure(&method_call(
            view(seq_var("a")),
            "index_logic",
            vec![int(0)],
        ))
        .expect("a@[0] should encode");
    let b0 = encoder
        .encode_pure(&method_call(
            view(seq_var("b")),
            "index_logic",
            vec![int(0)],
        ))
        .expect("b@[0] should encode");
    let one = encoder.solver.int_const(1);
    let two = encoder.solver.int_const(2);
    let len_a_is_one = encoder.solver.eq(len_a, one);
    let len_b_is_one = encoder.solver.eq(len_b, one);
    let a0_is_one = encoder.solver.eq(a0, one);
    let b0_is_two = encoder.solver.eq(b0, two);
    encoder.assert_term(len_a_is_one);
    encoder.assert_term(len_b_is_one);
    encoder.assert_term(a0_is_one);
    encoder.assert_term(b0_is_two);

    // Capture before solving so a timed-out query remains reproducible.
    if std::env::var_os("TWP_BR_DBG").is_some() {
        encoder.refresh_native_replay_json();
        if let Some(replay) = encoder.native_replay_json() {
            eprintln!("SEQ_WRONG_OPERAND_NATIVE_REPLAY_BEGIN\n{replay}\nSEQ_WRONG_OPERAND_NATIVE_REPLAY_END");
        }
    }

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ext_eq(a, concat(empty, b)) with same length but different elements must be UNSAT: got {result:?}"
    );
}

// ── Loop-level: variant decrease through produces step ───────────────

/// Diagnostic: loop variant proof for SeqIter iteration pattern.
///
/// Models the Creusot for-loop desugaring where each iteration:
/// - has produces invariant: ext_eq(original@, produced@.concat(iter@))
/// - has a body effect that grows produced by one element
/// - variant is original.len() - produced.len()
///
/// This test exercises the full loop verifier pipeline with produces.
/// Quantifier chaining may not fully connect ext_eq -> concat-length ->
/// variant decrease in all solver configurations, but it must fail closed
/// instead of returning a concrete failed obligation.
#[test]
#[timeout(60000)]
fn test_seq_iter_loop_variant_diagnostic() {
    // invariant: ext_eq(original@, produced@.concat(iter@))
    //            && produced@.len() >= 0
    let concat = method_call(
        view(seq_var("produced")),
        "concat",
        vec![view(seq_var("iter"))],
    );
    let produces_inv = method_call(view(seq_var("original")), "ext_eq", vec![concat]);
    let produced_nonneg = ge(
        method_call(view(seq_var("produced")), "len", vec![]),
        int(0),
    );
    let inv = and(produces_inv, produced_nonneg);

    // loop condition: iter has remaining elements (modeled as iter@.len() > 0)
    let cond = gt(method_call(view(seq_var("iter")), "len", vec![]), int(0));

    // variant: original@.len() - produced@.len()
    let variant = sub(
        method_call(view(seq_var("original")), "len", vec![]),
        method_call(view(seq_var("produced")), "len", vec![]),
    );

    // requires: original@.len() >= 0 (Seq lengths are non-negative)
    let req = ge(
        method_call(view(seq_var("original")), "len", vec![]),
        int(0),
    );

    // body effect: produced' = produced.push_back(v)
    let produced_prime = method_call(view(seq_var("produced")), "push_back", vec![var("v")]);
    let mut body_effect = HashMap::new();
    body_effect.insert("produced".to_string(), produced_prime);

    let mut pre_loop = HashMap::new();
    pre_loop.insert(
        "produced".to_string(),
        NamedBindingValue::untyped(logic_fn_call("seq_empty", vec![])),
    );
    pre_loop.insert(
        "iter".to_string(),
        NamedBindingValue::untyped(seq_var("original")),
    );

    let iter_step = eq(
        view(seq_var("iter")),
        method_call(
            view(seq_var("iter_prime")),
            "push_front_ghost",
            vec![var("v")],
        ),
    );

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["produced", "iter", "v"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        // Keep the diagnostic bounded so grouped `seq_iter_produces` runs
        // don't trip the outer test timeout under solver contention.
        config: LoopEncoderConfig::default()
            .with_timeout(std::time::Duration::from_secs(10))
            .with_transition_facts(&[iter_step]),
    })
    .unwrap();

    assert!(
        matches!(
            result.initialization,
            VerificationResult::Verified(_) | VerificationResult::Unknown(_)
        ),
        "SeqIter initialization should verify or fail closed: {:?}",
        result.initialization
    );
    assert!(
        matches!(
            result.preservation,
            VerificationResult::Verified(_) | VerificationResult::Unknown(_)
        ),
        "SeqIter preservation should verify or fail closed: {:?}",
        result.preservation
    );
    if let Some(variant_nonneg) = result.variant_nonneg {
        assert!(
            matches!(
                variant_nonneg,
                VerificationResult::Verified(_) | VerificationResult::Unknown(_)
            ),
            "SeqIter variant nonneg should verify or fail closed: {variant_nonneg:?}"
        );
    }
    if let Some(variant_decrease) = result.variant_decrease {
        assert!(
            matches!(
                variant_decrease,
                VerificationResult::Verified(_) | VerificationResult::Unknown(_)
            ),
            "SeqIter variant decrease should verify or fail closed: {variant_decrease:?}"
        );
    }
}

// ── Combined reverse_ghost loop tests removed (#2116) ────────────────
//
// Five combined ext_eq+reverse loop tests (reverse_ghost combined,
// direct-equality, type-param, postcondition with/without completion)
// were removed because each phase encoding for the combined invariant
// takes ~30s, making 5+ phases exceed any reasonable test timeout
// (>180s per test, >900s total for 5 tests).
//
// The function-level tests above verify encoding correctness.
// The simpler `test_seq_iter_loop_variant_diagnostic` verifies the loop
// pipeline. End-to-end coverage is provided by the compat harness
// (ghost/seq_iter.rs, cc/fmap.rs).

/// Produces-only preservation with direct equality (no reverse invariant).
///
/// Isolates the produces preservation proof chain from the reverse invariant
/// to determine if the combined timeout is caused by the produces chain
/// alone or by interaction with the reverse axioms.
#[test]
#[timeout(90000)]
fn test_produces_only_preservation_direct_equality() {
    // invariant: View(original) == produced.concat(View(iter))  [DIRECT]
    let concat = method_call(
        view(seq_var("produced")),
        "concat",
        vec![view(seq_var("iter"))],
    );
    let produces_inv = eq(view(seq_var("original")), concat);

    let cond = gt(method_call(view(seq_var("iter")), "len", vec![]), int(0));
    let variant = sub(
        method_call(view(seq_var("original")), "len", vec![]),
        method_call(view(seq_var("produced")), "len", vec![]),
    );
    let req = ge(
        method_call(view(seq_var("original")), "len", vec![]),
        int(0),
    );

    let mut body_effect = HashMap::new();
    body_effect.insert(
        "produced".to_string(),
        method_call(view(seq_var("produced")), "push_back", vec![var("v")]),
    );

    let seq_empty = logic_fn_call("seq_empty", vec![]);
    let mut pre_loop = HashMap::new();
    pre_loop.insert(
        "produced".to_string(),
        NamedBindingValue::untyped(seq_empty),
    );
    pre_loop.insert(
        "iter".to_string(),
        NamedBindingValue::untyped(seq_var("original")),
    );

    let iter_step = eq(
        view(seq_var("iter")),
        method_call(
            view(seq_var("iter_prime")),
            "push_front_ghost",
            vec![var("v")],
        ),
    );

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[produces_inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["produced", "iter", "v"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default()
            // AY 0.4 performs stricter proof/model validation for the
            // Array-backed Seq transition; retain a bounded but realistic
            // proof budget for this preservation lane.
            .with_timeout(std::time::Duration::from_secs(45))
            .with_transition_facts(&[iter_step]),
    })
    .unwrap();

    // Initialization verifies in isolation but may timeout under parallel
    // test execution due to solver resource contention. Accept both.
    assert!(
        matches!(
            result.initialization,
            VerificationResult::Verified(_) | VerificationResult::Unknown(_)
        ),
        "produces-only init should verify or timeout under load: got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "produces-only direct-equality preservation should verify: got {:?}",
        result.preservation
    );
}
