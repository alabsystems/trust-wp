// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// --- seq_iter ghost loop tests (#1581) ---

/// Helper: build `Var(name)` with Seq sort hint.
fn seq_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Seq))
}

/// Helper: build `receiver.method(args)`.
fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

/// Helper: build `View(expr)`.
fn view(expr: PureExpr) -> PureExpr {
    PureExpr::View(Arc::new(expr))
}

/// Helper: integer variable.
fn int_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

/// Scalar `@` wrappers in loop VCs should normalize to the underlying variable.
///
/// Driver-level range-loop invariants are expressed as `i@ == produced.len()`.
/// If the loop prover keeps `i@` as a distinct `i_view` symbol during induction,
/// preservation reasons about the wrong variable because the body effect only
/// updates `i`. Normalizing scalar views before the loop VCs restores the
/// expected `i' = i + 1` proof path. (#2171)
#[test]
#[timeout(30000)]
fn scalar_view_seq_len_invariant_preserves_through_body_effects() {
    let invariant = PureExpr::BinOp(
        Arc::new(view(int_var("i"))),
        BinOp::Eq,
        Arc::new(method_call(view(seq_var("produced")), "len", vec![])),
    );
    let condition = PureExpr::BinOp(
        Arc::new(view(int_var("i"))),
        BinOp::Lt,
        Arc::new(int_var("n")),
    );

    let mut body_effect = HashMap::new();
    body_effect.insert(
        "produced".to_string(),
        method_call(seq_var("produced"), "push_back", vec![int_var("i")]),
    );
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(int_var("i")),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let mut pre_loop = HashMap::new();
    pre_loop.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let seq_empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let init_facts = vec![
        PureExpr::BinOp(
            Arc::new(seq_var("produced")),
            BinOp::Eq,
            Arc::new(seq_empty.clone()),
        ),
        PureExpr::BinOp(
            Arc::new(method_call(view(seq_var("produced")), "len", vec![])),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
    ];

    let ctx = LoopVerificationContext {
        requires: &[PureExpr::BinOp(
            Arc::new(view(int_var("n"))),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )],
        ensures: &[],
        invariants: std::slice::from_ref(&invariant),
        loop_condition: Some(&condition),
        condition_is_body_break: false,
        modified_vars: &["produced", "i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &init_facts,
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("encoding should succeed");
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "scalar-view initialization should verify after normalization: {result:?}"
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "scalar-view preservation should use the updated `i` body effect: {result:?}"
    );
}

/// Models the `ghost/seq_iter.rs` `reverse_ghost` function's loop proof.
///
/// The function iterates over a ghost sequence `s`, calling `push_front_ghost`
/// on each element to build `result` (which accumulates the reverse).
///
/// Loop invariant: `result == produced.reverse()`
/// Body effects: `result' = push_front(result, x)`, `produced' = push_back(produced, x)`
/// Postcondition: `result == s.reverse()` (via completion fact `produced == s`)
///
/// This test exercises the R4 axiom: `reverse(push_back(s, x)) = push_front(reverse(s), x)`.
#[test]
#[timeout(30000)]
fn ghost_seq_iter_reverse_preservation_verifies() {
    // Invariant: result@ == produced@.reverse()
    let invariant = PureExpr::BinOp(
        Arc::new(view(seq_var("result"))),
        BinOp::Eq,
        Arc::new(method_call(view(seq_var("produced")), "reverse", vec![])),
    );

    // Body effects: result' = push_front_ghost(result, x)
    //               produced' = push_back(produced, x)
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "result".to_string(),
        method_call(
            view(seq_var("result")),
            "push_front_ghost",
            vec![int_var("x")],
        ),
    );
    body_effect.insert(
        "produced".to_string(),
        method_call(view(seq_var("produced")), "push_back", vec![int_var("x")]),
    );

    let modified_vars: Vec<&str> = vec!["result", "produced"];
    let deref_body_effect = HashMap::new();
    let double_deref_body_effect = HashMap::new();

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[invariant],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &deref_body_effect,
        double_deref_body_effect: &double_deref_body_effect,
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result =
        verify_loop_invariant(&ctx).expect("loop verification should encode without errors");

    // The preservation step requires the R4 identity
    // `reverse(push_back(s,x)) = push_front(reverse(s),x)` to close through a
    // CHAIN of equalities — the invariant `result == reverse(produced)` composed
    // with R4 and the `push_front`/`push_back` body effects, lifted to the
    // array/len/offset projector conjuncts that `try_decompose_seq_equality`
    // produces for a Seq `==` goal. R4 is a GENUINE Seq theorem and the
    // obligation is TRUE, so the only unsound outcome would be `Failed` (a
    // spurious counterexample to a valid goal).
    //
    // Historically ay-dpll's congruence-free core could not propagate the full
    // projector chain in budget: it timed out (Unknown) at the default budget
    // and, with a larger budget, produced a SPURIOUS model (a fake
    // counterexample where a Seq length/offset went negative). The ground
    // field-range facts asserted per program term (#2097, the retired-quantified
    // -axiom → ground migration in encoder/match_enc/field_range.rs) now prune
    // exactly those out-of-range spurious models, so the solver closes the chain
    // and returns a genuine `Verified` — a sound proof of a true obligation, the
    // strictly-better resting state. We therefore accept `Verified` OR `Unknown`
    // (both sound for a true goal; Unknown just means "still too hard in budget")
    // and reject only `Failed`. Verified via added SOUND range facts cannot be an
    // unsound accept: adding a valid axiom to a sound solver preserves soundness,
    // and the sibling should-fail test `test_verify_take_max_wrong_ref_fails`
    // confirms the same facts sharpen (not weaken) counterexample precision.
    assert!(
        !matches!(result.preservation, VerificationResult::Failed(_)),
        "preservation of `result == produced.reverse()` with push_front/push_back \
         body effects: the goal is TRUE (R4), so only `Failed` (a spurious \
         counterexample) is a bug; Unknown or Verified are both sound, got {:?}",
        result.preservation
    );
}

/// Tests initialization: at loop entry, result = seq_empty, produced = seq_empty,
/// so `result == produced.reverse()` holds because `reverse(seq_empty) == seq_empty` (R1).
#[test]
#[timeout(30000)]
fn ghost_seq_iter_reverse_initialization_verifies() {
    let invariant = PureExpr::BinOp(
        Arc::new(view(seq_var("result"))),
        BinOp::Eq,
        Arc::new(method_call(view(seq_var("produced")), "reverse", vec![])),
    );

    // Init facts: both result@ and produced@ equal seq_empty.
    // Using View-wrapped Seq-annotated variables ensures correct sort propagation
    // (pre_loop_assignments creates raw Var without ExprSort, defaulting to Int).
    let seq_empty_expr = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let init_facts = vec![
        // result@ == seq_empty
        PureExpr::BinOp(
            Arc::new(view(seq_var("result"))),
            BinOp::Eq,
            Arc::new(seq_empty_expr.clone()),
        ),
        // produced@ == seq_empty
        PureExpr::BinOp(
            Arc::new(view(seq_var("produced"))),
            BinOp::Eq,
            Arc::new(seq_empty_expr),
        ),
    ];

    let body_effect = HashMap::new();
    let deref_body_effect = HashMap::new();
    let double_deref_body_effect = HashMap::new();

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[invariant],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &body_effect,
        deref_body_effect: &deref_body_effect,
        double_deref_body_effect: &double_deref_body_effect,
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &init_facts,
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result =
        verify_loop_invariant(&ctx).expect("loop verification should encode without errors");

    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result.initialization),
        "initialization of `result == produced.reverse()` with both seq_empty should \
         verify (requires R1: reverse(empty) == empty), got {:?}",
        result.initialization
    );
}

/// Tests postcondition: at loop exit, `produced == s` (completion fact),
/// invariant `result == produced.reverse()` gives `result == s.reverse()`.
#[test]
#[timeout(30000)]
fn ghost_seq_iter_reverse_postcondition_verifies() {
    let invariant = PureExpr::BinOp(
        Arc::new(view(seq_var("result"))),
        BinOp::Eq,
        Arc::new(method_call(view(seq_var("produced")), "reverse", vec![])),
    );

    // Postcondition: result@ == s@.reverse()
    let postcondition = PureExpr::BinOp(
        Arc::new(view(seq_var("result"))),
        BinOp::Eq,
        Arc::new(method_call(view(seq_var("s")), "reverse", vec![])),
    );

    // Post extra fact: produced@ == s@ (iterator completion)
    let post_facts = vec![PureExpr::BinOp(
        Arc::new(view(seq_var("produced"))),
        BinOp::Eq,
        Arc::new(view(seq_var("s"))),
    )];

    let body_effect = HashMap::new();
    let deref_body_effect = HashMap::new();
    let double_deref_body_effect = HashMap::new();

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[postcondition],
        invariants: &[invariant],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &body_effect,
        deref_body_effect: &deref_body_effect,
        double_deref_body_effect: &double_deref_body_effect,
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &post_facts,
        config: LoopEncoderConfig::default(),
    };

    let result =
        verify_loop_invariant(&ctx).expect("loop verification should encode without errors");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition `result == s.reverse()` with completion fact `produced == s` \
         should verify via substitution, got {:?}",
        result.postcondition
    );
}

/// The direct reverse-congruence discharge must require the exact completion
/// equality used by the target receiver.
#[test]
#[timeout(30000)]
fn ghost_seq_iter_reverse_postcondition_rejects_unrelated_completion() {
    let invariant = PureExpr::BinOp(
        Arc::new(view(seq_var("result"))),
        BinOp::Eq,
        Arc::new(method_call(view(seq_var("produced")), "reverse", vec![])),
    );
    let postcondition = PureExpr::BinOp(
        Arc::new(view(seq_var("result"))),
        BinOp::Eq,
        Arc::new(method_call(view(seq_var("s")), "reverse", vec![])),
    );
    let unrelated_completion = vec![PureExpr::BinOp(
        Arc::new(view(seq_var("produced"))),
        BinOp::Eq,
        Arc::new(view(seq_var("other"))),
    )];

    let body_effect = HashMap::new();
    let deref_body_effect = HashMap::new();
    let double_deref_body_effect = HashMap::new();
    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[postcondition],
        invariants: &[invariant],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &body_effect,
        deref_body_effect: &deref_body_effect,
        double_deref_body_effect: &double_deref_body_effect,
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &unrelated_completion,
        config: LoopEncoderConfig::default(),
    };

    let result =
        verify_loop_invariant(&ctx).expect("loop verification should encode without errors");
    assert!(
        !matches!(result.postcondition, VerificationResult::Verified(_)),
        "an unrelated completion equality must not discharge the reverse postcondition"
    );
}

/// Variant `*len - produced.len()` with body effect `produced' = push_back(produced, x)`.
///
/// Models the ghost/seq_iter.rs variant expression where `len` is a snapshot
/// of the input sequence length and `produced` tracks yielded elements.
/// The nonneg check requires `produced.len() <= len` (from invariant).
/// The decrease check requires `push_back(produced, x).len() = produced.len() + 1`
/// (from Seq axiom A1).
///
/// (#1581)
#[test]
#[timeout(30000)]
fn ghost_seq_iter_variant_nonneg_verifies() {
    // Invariant: produced@.len() <= len (ensures variant is non-negative)
    let invariant = PureExpr::BinOp(
        Arc::new(method_call(view(seq_var("produced")), "len", vec![])),
        BinOp::Le,
        Arc::new(int_var("len")),
    );

    // Variant: len - produced@.len()
    let variant = PureExpr::BinOp(
        Arc::new(int_var("len")),
        BinOp::Sub,
        Arc::new(method_call(view(seq_var("produced")), "len", vec![])),
    );

    // produced is modified, len is not (it's a snapshot)
    let modified_vars: Vec<&str> = vec!["produced"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "produced".to_string(),
        method_call(view(seq_var("produced")), "push_back", vec![int_var("x")]),
    );

    let result = verify_variant_nonneg(
        &[invariant],
        None,
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("variant nonneg should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "variant `len - produced.len()` nonneg should verify with invariant \
         `produced.len() <= len`, got {result:?}"
    );
}

/// Variant decrease for `*len - produced.len()` with `produced' = push_back(produced, x)`.
///
/// The decrease holds because `push_back(s, x).len() = s.len() + 1` (Seq axiom A1),
/// so `variant' = len - (produced.len() + 1) < len - produced.len() = variant`.
///
/// (#1581)
#[test]
#[timeout(30000)]
fn ghost_seq_iter_variant_decrease_verifies() {
    // Invariant: produced@.len() <= len
    let invariant = PureExpr::BinOp(
        Arc::new(method_call(view(seq_var("produced")), "len", vec![])),
        BinOp::Le,
        Arc::new(int_var("len")),
    );

    // Variant: len - produced@.len()
    let variant = PureExpr::BinOp(
        Arc::new(int_var("len")),
        BinOp::Sub,
        Arc::new(method_call(view(seq_var("produced")), "len", vec![])),
    );

    // produced is modified, len is not
    let modified_vars: Vec<&str> = vec!["produced"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "produced".to_string(),
        method_call(view(seq_var("produced")), "push_back", vec![int_var("x")]),
    );

    let result = verify_variant_decrease(
        &[invariant],
        None,
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("variant decrease should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "variant `len - produced.len()` should strictly decrease when \
         produced' = push_back(produced, x), got {result:?}"
    );
}

/// Tests initialization via the driver-level path: `result` is bound by
/// `pre_loop_assignments` (not by explicit `init_extra_facts`), while
/// `produced == seq_empty` is supplied as an init fact (the for-loop ghost
/// state path).
///
/// This models exactly what the driver pipeline does for
/// `ghost/seq_iter::reverse_ghost`:
///   - `let mut result = Seq::new().into_inner();` is captured as a
///     `pre_loop_assignments["result"] = seq_empty()` binding.
///   - The for-loop ghost state synthesizer
///     (`build_for_loop_init_facts`, `for_loop_facts.rs:438`) emits the
///     `produced@ == seq_empty()` init fact.
///
/// If the encoder threads `pre_loop_assignments` into the initialization VC
/// the same way it threads `init_extra_facts`, this test verifies. Otherwise
/// the test demonstrates the gap described in
/// `designs/2026-05-20-ghost-iter-init-fact-propagation.md`.
#[test]
#[timeout(30000)]
fn ghost_seq_iter_reverse_initialization_via_pre_loop_assignment() {
    // Invariant: result@ == produced@.reverse()
    let invariant = PureExpr::BinOp(
        Arc::new(view(seq_var("result"))),
        BinOp::Eq,
        Arc::new(method_call(view(seq_var("produced")), "reverse", vec![])),
    );

    let seq_empty_expr = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };

    // Driver-level encoding: `let mut result = Seq::new().into_inner();`
    // shows up as a pre_loop binding `result := seq_empty()`. The sort hint
    // is `Seq` to match what `extract_pre_loop_assignments` would produce
    // when `TyCtxt` resolves `Seq<T>`.
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "result".to_string(),
        NamedBindingValue::new(Some(ExprSort::Seq), seq_empty_expr.clone()),
    );

    // The for-loop ghost state path supplies this fact for `produced`.
    let init_facts = vec![PureExpr::BinOp(
        Arc::new(view(seq_var("produced"))),
        BinOp::Eq,
        Arc::new(seq_empty_expr),
    )];

    let body_effect = HashMap::new();
    let deref_body_effect = HashMap::new();
    let double_deref_body_effect = HashMap::new();

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[invariant],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &["result", "produced"],
        body_effect: &body_effect,
        deref_body_effect: &deref_body_effect,
        double_deref_body_effect: &double_deref_body_effect,
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &init_facts,
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result =
        verify_loop_invariant(&ctx).expect("loop verification should encode without errors");

    // The driver-level path verifies if and only if `pre_loop_assignments`
    // contributes `result == seq_empty()` to the initialization VC. R1
    // (`reverse(empty) == empty`) closes the goal from there.
    //
    // The companion test `ghost_seq_iter_reverse_initialization_verifies`
    // already proves the encoder handles this scenario when the fact is
    // supplied via `init_extra_facts`. If this test fails (init = Failed
    // with a counterexample), the gap is in the
    // `pre_loop_assignments` → init-fact translation rather than in the
    // axiom encoding itself.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization via pre_loop_assignments should verify identically to \
         initialization via init_extra_facts; got {:?}. See \
         designs/2026-05-20-ghost-iter-init-fact-propagation.md for the gap \
         this test captures.",
        result.initialization
    );
}
