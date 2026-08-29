// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding (Part of #111).
//!
//! Includes sequence view, len, index, `push_back`, error handling, and axiom tests.
//! Split from encoding.rs per #395.

use super::*;

// =============================================================================
// Seq contains() Tests (#699, #855 AC5)
// =============================================================================

/// Test that v@.contains(x) encodes successfully via Seq path when the receiver
/// is pre-hinted as Seq via `register_sort_hints`. The `contains` method is
/// shared between Seq and FSet, so sort hints are required for correct dispatch.
#[test]
#[timeout(30000)]
fn test_encode_seq_contains_basic() {
    let mut encoder = AYEncoder::new();

    let v_view = view(var("v"));

    // Pre-scan with v@.len() to hint v_view as Seq (len on View is unambiguous)
    let len_hint = method_call(v_view.clone(), "len", vec![]);

    // v@.contains(42)
    let expr = method_call(v_view, "contains", vec![int(42)]);

    encoder.register_sort_hints(&[len_hint, expr.clone()]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "v@.contains(42) encoding should succeed via Seq path: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "Seq functions should be initialized after encoding contains()"
    );
}

/// Axiom 10: contains(push_back(s, v), x) = (x == v || contains(s, x)).
///
/// After pushing 42, the sequence must contain 42.
/// Encodes: NOT(v@.push_back(42).contains(42)) and checks UNSAT.
/// Uses push_back as receiver which unambiguously identifies Seq (no hints needed).
#[test]
#[timeout(30000)]
fn test_seq_axiom_contains_after_push_back() {
    let mut encoder = AYEncoder::new();

    let v_view = view(var("v"));

    // v@.push_back(42).contains(42) — push_back is uniquely Seq
    let push_back = method_call(v_view, "push_back", vec![int(42)]);
    let contains_42 = method_call(push_back, "contains", vec![int(42)]);

    let formula_term = encoder
        .encode_pure(&contains_42)
        .expect("push_back + contains should encode");

    let neg = encoder.solver.not(formula_term);
    encoder.assert_term(neg);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT(contains(push_back(v, 42), 42)) should be UNSAT (axiom 10), got {result:?}"
    );
}

/// Axiom 10 non-tautology control: push_back(empty, 42).contains(43) is false.
///
/// This concrete negative theorem proves the axiom test above
/// (`test_seq_axiom_contains_after_push_back`) is not vacuously passing due to
/// `contains` always returning true. We assert the known-false membership and
/// require a certified refutation: asking AY for a SAT witness in the presence
/// of the universal sequence axioms enters its intentionally unsupported
/// quantified model-finalization lane, whereas the refutation is exactly the
/// proof-bearing authority this test needs.
#[test]
#[timeout(30000)]
fn test_seq_axiom_contains_push_back_is_contingent() {
    let mut encoder = AYEncoder::new();

    let empty = logic_fn_call("seq_empty", vec![]);
    let push_back = method_call(empty, "push_back", vec![int(42)]);
    let contains_43 = method_call(push_back, "contains", vec![int(43)]);

    let formula_term = encoder
        .encode_pure(&contains_43)
        .expect("push_back + contains should encode");

    // Assert push_back(empty, 42).contains(43). Axiom 9 makes the prior
    // membership false and axiom 10 reduces this assertion to false.
    encoder.assert_term(formula_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "contains(push_back(empty, 42), 43) should be Unsat, got {result:?}"
    );
}

// =============================================================================
// Seq Array+Length Encoding Tests (#1317)
// =============================================================================

/// Array+Length encoding proves chained push_back length facts via ay's
/// native Array theory (store/select) without quantifier chaining.
#[test]
#[timeout(30000)]
fn test_seq_array_push_back_chain_len() {
    let mut encoder = AYEncoder::new();

    let chain = method_call(
        method_call(
            logic_fn_call("seq_empty", vec![]),
            "push_back",
            vec![int(10)],
        ),
        "push_back",
        vec![int(20)],
    );
    let len_expr = method_call(chain, "len", vec![]);
    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("push_back chain len encoding should succeed");

    let two = encoder.solver.int_const(2);
    let violation = encoder.solver.neq(len_term, two);
    encoder.assert_term(violation);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "len(push_back(push_back(empty,10),20)) != 2 should be Unsat, got {result:?}"
    );
}

/// Array+Length set encoding: index(set(s, i, v), i) = v via store/select.
#[test]
#[timeout(30000)]
fn test_seq_array_set_write_read_same() {
    let mut encoder = AYEncoder::new();

    let set_expr = method_call(
        method_call(
            logic_fn_call("seq_empty", vec![]),
            "push_back",
            vec![int(10)],
        ),
        "set",
        vec![int(0), int(99)],
    );
    let read_expr = method_call(set_expr, "index_logic", vec![int(0)]);
    let read_term = encoder
        .encode_pure(&read_expr)
        .expect("set/index_logic encoding should succeed");

    let ninety_nine = encoder.solver.int_const(99);
    let violation = encoder.solver.neq(read_term, ninety_nine);
    encoder.assert_term(violation);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "index(set(push_back(empty,10),0,99),0) != 99 should be Unsat, got {result:?}"
    );
}

/// Array+Length subsequence encoding: len(subsequence(s, from, to)) = max(0, to-from).
#[test]
#[timeout(30000)]
fn test_seq_array_subsequence_len() {
    let mut encoder = AYEncoder::new();

    let base = method_call(
        method_call(
            method_call(
                logic_fn_call("seq_empty", vec![]),
                "push_back",
                vec![int(1)],
            ),
            "push_back",
            vec![int(2)],
        ),
        "push_back",
        vec![int(3)],
    );
    let subseq = method_call(base, "subsequence", vec![int(1), int(3)]);
    let len_expr = method_call(subseq, "len", vec![]);
    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("subsequence len encoding should succeed");

    let expected_len = encoder.solver.int_const(2);
    let violation = encoder.solver.neq(len_term, expected_len);
    encoder.assert_term(violation);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "len(subsequence(push_back^3(empty),1,3)) != 2 should be Unsat, got {result:?}"
    );
}

/// Array+Length singleton encoding: len(singleton(v)) = 1 and index(singleton(v),0) = v.
#[test]
#[timeout(30000)]
fn test_seq_array_singleton_len_and_index() {
    let mut encoder = AYEncoder::new();

    let singleton = logic_fn_call("seq", vec![int(7)]);
    let len_expr = method_call(singleton.clone(), "len", vec![]);
    let idx_expr = method_call(singleton, "index_logic", vec![int(0)]);

    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("singleton len encoding should succeed");
    let idx_term = encoder
        .encode_pure(&idx_expr)
        .expect("singleton index encoding should succeed");

    let one = encoder.solver.int_const(1);
    let seven = encoder.solver.int_const(7);
    let len_ok = encoder.solver.eq(len_term, one);
    let idx_ok = encoder.solver.eq(idx_term, seven);
    let both_ok = encoder.solver.and(len_ok, idx_ok);
    let violation = encoder.solver.not(both_ok);
    encoder.assert_term(violation);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "singleton ground facts (len=1 and index(0)=7) should be provable, got {result:?}"
    );
}

/// Seq-level structural equality: set(push_back(empty, 1), 0, 1) == push_back(empty, 1).
///
/// With Seq equality decomposition (#1317), the equality is reduced to
/// component-wise Array+Length+Offset comparison:
///   arr(set(pb(empty,1),0,1)) == arr(pb(empty,1))  → Array extensional eq
///   len(set(pb(empty,1),0,1)) == len(pb(empty,1))  → 1 == 1
///   off(set(pb(empty,1),0,1)) == off(pb(empty,1))  → 0 == 0
///
/// The Array equality reduces via read-over-write (store(store(const(0),0,1),0,1)
/// vs store(const(0),0,1) — the outer store is idempotent) and is decidable
/// by ay's native Array theory.
#[test]
#[timeout(30000)]
fn test_seq_array_equality_extensionality() {
    let mut encoder = AYEncoder::new();

    let base = method_call(
        logic_fn_call("seq_empty", vec![]),
        "push_back",
        vec![int(1)],
    );
    let rewritten = method_call(base.clone(), "set", vec![int(0), int(1)]);
    let eq_expr = eq(rewritten, base);
    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("seq equality encoding should succeed");

    let violation = encoder.solver.not(eq_term);
    encoder.assert_term(violation);

    let result = encoder.check_sat();
    // With Seq equality decomposition (#1317), the equality is decidable via
    // ay's native Array theory. The negation is UNSAT.
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "set(base,0,1) equality should verify via Array+Length decomposition, got {result:?}"
    );
}

/// Seq equality decomposition: set(seq![0,0,0,0], 1, 1) == seq![0,1,0,0] (#1317).
///
/// Models the `slices/range.rs` postcondition pattern where a concrete Seq
/// (from IndexMut point-write synthesis) must equal a `seq![...]` literal.
/// Without equality decomposition, ay-dpll returns Unknown because uninterpreted
/// Seq sort equality cannot leverage Array theory. With decomposition, the
/// equality reduces to Array+Length+Offset component comparisons.
#[test]
#[timeout(30000)]
fn test_seq_equality_decomposition_concrete_point_write() {
    use ay_dpll::api::SolveResult;

    let mut encoder = AYEncoder::new();

    // Build: set(seq![0, 0, 0, 0], 1, 1)
    let base = logic_fn_call("seq", vec![int(0), int(0), int(0), int(0)]);
    let updated = method_call(base, "set", vec![int(1), int(1)]);

    // Target: seq![0, 1, 0, 0]
    let target = logic_fn_call("seq", vec![int(0), int(1), int(0), int(0)]);

    // Encode equality: set(seq![0,0,0,0], 1, 1) == seq![0,1,0,0]
    let eq_expr = eq(updated, target);
    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("seq equality encoding should succeed");

    // Assert negation: NOT(updated == target)
    // The decomposition fires (Seq eq → Array+Length+Offset eq) but ay-dpll's
    // Array theory cannot yet prove store-override extensional equality:
    //   store(store(store(store(C,0,0),1,0),2,0),3,0)[1←1]
    //   vs store(store(store(store(C,0,0),1,1),2,0),3,0)
    // This verifies the decomposition path doesn't crash and produces a Bool term.
    //
    // The correct answer for the negation is Sat (the equality IS true, so
    // its negation is unsatisfiable... wait, no: the negation of a true
    // equality is Unsat). Actually: set(seq![0,0,0,0],1,1) should equal
    // seq![0,1,0,0], so the equality is true, and its negation is Unsat.
    //
    // ay rev 702bf7 was returning Sat for the equality (spurious).
    // The correct answer is Unsat.
    let violation = encoder.solver.not(eq_term);
    encoder.assert_term(violation);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "set(seq![0,0,0,0],1,1)==seq![0,1,0,0] negated should be Unsat \
         Got {result:?}"
    );
}

/// IndexMut SeqValue synthesis: the point-write postcondition
///     `(^a)@.index_logic(idx@) == ^result`
/// from an IndexMut call-site assumption should produce a concrete SeqValue
/// for the final view variable, enabling Array-theory verification of
///     `(^a)@.index_logic(2) == 3`
/// without quantifier reasoning.
///
/// Models `index_mut_slice` from `slices/01.rs`:
/// ```rust
/// #[requires(a@.len() == 5)]
/// #[ensures((^a)[2]@ == 3)]
/// fn index_mut_slice(a: &mut [u32]) {
///     a[2] = 3;
/// }
/// ```
///
/// Part of #1317.
#[test]
#[timeout(60000)]
fn test_index_mut_seq_value_synthesis_verifies_point_write() {
    use crate::verify::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // User precondition: a@.len() == 5
    let user_req = eq(method_call(view(var("a")), "len", vec![]), int(5));

    // Call-site assumptions from IndexMut postconditions:
    // 1. *_5 == a@.index_logic(2@)  (read old value)
    let call_a1 = eq(
        PureExpr::Deref(Arc::new(var("_5"))),
        method_call(view(var("a")), "index_logic", vec![view(var("idx"))]),
    );
    // 2. (^a)@.index_logic(2@) == ^_5  (point-write)
    let call_a2 = eq(
        method_call(
            view(final_expr(var("a"))),
            "index_logic",
            vec![view(var("idx"))],
        ),
        final_expr(var("_5")),
    );
    // 3. (^a)@.len() == a@.len()  (length preservation)
    let call_a3 = eq(
        method_call(view(final_expr(var("a"))), "len", vec![]),
        method_call(view(var("a")), "len", vec![]),
    );

    // idx@ == 2 (the index is the literal 2)
    let idx_binding = eq(view(var("idx")), int(2));
    // ^_5 == 3 (the write-through: *_5 = 3 means ^_5 = 3)
    let write_through = eq(final_expr(var("_5")), int(3));

    let requires = vec![
        user_req,
        call_a1,
        call_a2,
        call_a3,
        idx_binding,
        write_through,
    ];

    // Postcondition: (^a)@.index_logic(2) == 3
    let ensures = vec![eq(
        method_call(view(final_expr(var("a"))), "index_logic", vec![int(2)]),
        int(3),
    )];

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .timeout(Some(std::time::Duration::from_secs(45))),
    );
    let result = result.expect("encoding should succeed");
    match &result {
        VerificationResult::Verified(_) => {}
        other => panic!("index_mut point-write should verify, got {other:?}"),
    }
}

/// Lower-level encoder test for IndexMut SeqValue synthesis (#1317).
#[test]
#[timeout(30000)]
fn test_index_mut_seq_value_synthesis_encoder_level() {
    use ay_dpll::api::SolveResult;
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Helper: encode, assert, and optionally run synthesis.
    fn encode_assert(enc: &mut AYEncoder, expr: &PureExpr, synthesize: bool) {
        let t = enc.encode_pure(expr).unwrap();
        enc.assert_term(t);
        if synthesize {
            enc.try_synthesize_index_mut_seq_value(expr, None)
                .expect("index_mut synthesis should not fail");
        }
    }

    let fa_view = view(final_expr(var("a")));
    let a_view = view(var("a"));
    let hints = vec![
        eq(method_call(a_view.clone(), "len", vec![]), int(5)),
        eq(
            method_call(fa_view.clone(), "index_logic", vec![view(var("idx"))]),
            final_expr(var("_5")),
        ),
        eq(
            method_call(fa_view.clone(), "len", vec![]),
            method_call(a_view.clone(), "len", vec![]),
        ),
        eq(
            method_call(fa_view.clone(), "index_logic", vec![int(2)]),
            int(3),
        ),
    ];
    encoder.register_sort_hints(&hints);
    encoder.register_formula_sort_hints(&hints);

    // Requires with synthesis on point-write and length assumptions.
    encode_assert(&mut encoder, &hints[0], true); // a@.len() == 5
    encode_assert(&mut encoder, &hints[1], true); // (^a)@[idx@] == ^_5
    encode_assert(&mut encoder, &hints[2], false); // (^a)@.len() == a@.len()
    encode_assert(&mut encoder, &eq(view(var("idx")), int(2)), false);
    encode_assert(&mut encoder, &eq(final_expr(var("_5")), int(3)), false);
    // Negate postcondition: NOT((^a)@.index_logic(2) == 3)
    let post_term = encoder.encode_pure(&hints[3]).unwrap();
    let neg_post = encoder.solver.not(post_term);
    encoder.assert_term(neg_post);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "point-write synthesis should make postcondition provable (UNSAT), got {result:?}"
    );
}

// =============================================================================
// Target test pattern proofs (#1317: index_range, slices/01, vector/07_read_write)
// =============================================================================

/// Prove index_range.rs pattern: 5 push_backs, each index returns its value.
///
/// Builds: push_back(push_back(push_back(push_back(push_back(empty, 0), 1), 2), 3), 4)
/// Proves: result[k] == k for k=0..4 (negated conjunction is UNSAT).
/// This is the core #1317 target test — must get UNSAT, not Unknown.
#[test]
#[timeout(30000)]
fn test_target_index_range_pattern() {
    use ay_dpll::api::SolveResult;

    let mut encoder = AYEncoder::new();

    // Build the push_back chain: empty, 0, 1, 2, 3, 4
    let empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let mut chain = empty;
    for k in 0..5 {
        chain = method_call(chain, "push_back", vec![int(k)]);
    }

    // For each index k, prove chain[k] == k
    for k in 0..5i64 {
        let idx_expr = method_call(chain.clone(), "index_logic", vec![int(k)]);
        let check = eq(idx_expr, int(k));

        let mut enc = AYEncoder::new();
        let term = enc.encode_pure(&check).expect("encode_pure");
        let negated = enc.solver.not(term);
        enc.assert_term(negated);
        let result = enc.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "push_back_chain[{k}] != {k} should be UNSAT (Array read-over-write), got {result:?}"
        );
    }

    // Also prove the length is 5
    let len_expr = method_call(chain, "len", vec![]);
    let len_check = eq(len_expr, int(5));
    let term = encoder.encode_pure(&len_check).expect("encode_pure");
    let negated = encoder.solver.not(term);
    encoder.assert_term(negated);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "push_back_chain.len() != 5 should be UNSAT, got {result:?}"
    );
}

/// Prove slices/01.rs pattern: set(seq, 2, 3).index_logic(2) == 3 with symbolic base.
///
/// Simulates the IndexMut postcondition pattern where a view-based sequence
/// has a single element written and the postcondition verifies the write.
#[test]
#[timeout(30000)]
fn test_target_slices01_point_write_pattern() {
    use ay_dpll::api::SolveResult;

    // Build: set(push_back(push_back(push_back(empty, 10), 20), 30), 2, 3)
    // Prove: result[2] == 3
    let empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let base = method_call(
        method_call(
            method_call(empty, "push_back", vec![int(10)]),
            "push_back",
            vec![int(20)],
        ),
        "push_back",
        vec![int(30)],
    );
    let updated = method_call(base, "set", vec![int(2), int(3)]);
    let read_back = method_call(updated, "index_logic", vec![int(2)]);
    let check = eq(read_back, int(3));

    let mut encoder = AYEncoder::new();
    let term = encoder.encode_pure(&check).expect("encode_pure");
    let negated = encoder.solver.not(term);
    encoder.assert_term(negated);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "set([10,20,30], 2, 3)[2] != 3 should be UNSAT (store-select-same), got {result:?}"
    );
}

/// Prove vector/07_read_write.rs pattern: set(seq, i, x).index_logic(i) == x
/// with SYMBOLIC index i.
///
/// This is the critical symbolic-index case where uninterpreted functions
/// cannot decide but Array theory's read-over-write-same law handles directly.
#[test]
#[timeout(30000)]
fn test_target_vector07_symbolic_write_read() {
    use ay_dpll::api::SolveResult;

    // Build: set(push_back(empty, 42), i, x).index_logic(i) == x
    // where i and x are symbolic (forall i, x)
    let empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let base = method_call(empty, "push_back", vec![int(42)]);
    let updated = method_call(base, "set", vec![var("i"), var("x")]);
    let read_back = method_call(updated, "index_logic", vec![var("i")]);
    let check = eq(read_back, var("x"));

    let mut encoder = AYEncoder::new();
    let term = encoder.encode_pure(&check).expect("encode_pure");
    let negated = encoder.solver.not(term);
    encoder.assert_term(negated);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "set(s, i, x)[i] != x should be UNSAT (symbolic store-select-same), got {result:?}"
    );
}

/// Prove set frame property with symbolic index: set(seq, i, x)[j] == seq[j] when i != j.
///
/// This is the frame condition needed for slices/01.rs where writing at one index
/// must not affect other indices.
#[test]
#[timeout(30000)]
fn test_target_set_frame_symbolic() {
    use ay_dpll::api::SolveResult;

    let empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };
    let base = method_call(
        method_call(empty, "push_back", vec![int(10)]),
        "push_back",
        vec![int(20)],
    );
    // set(base, 0, 99) — write 99 at index 0
    let updated = method_call(base, "set", vec![int(0), int(99)]);
    // Read at index 1 — should still be 20
    let read_at_1 = method_call(updated, "index_logic", vec![int(1)]);
    let check = eq(read_at_1, int(20));

    let mut encoder = AYEncoder::new();
    let term = encoder.encode_pure(&check).expect("encode_pure");
    let negated = encoder.solver.not(term);
    encoder.assert_term(negated);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "set(s, 0, 99)[1] != 20 should be UNSAT (store-select-different), got {result:?}"
    );
}

// =============================================================================
// Flat Call-Site Assumption Tests (#1317 e2e gap)
// =============================================================================

/// Verify that flat push_back assumptions with len==0 base produce UNSAT
/// postconditions via Array+Length encoding.
///
/// Simulates the exact e2e pattern from `index_range.rs::create_arr`:
///   requires: call_1_view.len() == 0
///   requires: final_call_1_view == call_1_view.push_back(0)
///   requires: final_call_1_view == call_1_view.push_back(1)
///   ...
///   requires: final_call_1_view == call_1_view.push_back(4)
///
/// Helper: assert negated equality is UNSAT (push/check_sat/pop pattern).
fn assert_negated_eq_unsat(encoder: &mut AYEncoder, lhs: Term, rhs: Term, context: &str) {
    let eq_term = encoder.solver.eq(lhs, rhs);
    encoder.solver.push();
    let neg = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neg);
    let result = encoder.check_sat();
    encoder.solver.pop();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Negated {context} should be UNSAT, got {result:?}"
    );
}

/// After flat push_back chain reconstruction, postcondition queries on the
/// target variable resolve via read-over-write (select on store chains).
///
/// Full create_arr pattern: 5 flat push_back values [0..4], chain reconstruction
/// synthesizes `store(store(store(store(store(const_array(0), 0, 0), 1, 1), 2, 2), 3, 3), 4, 4)`.
/// Postcondition: `result@.len() == 5 && result[0]@ == 0 && ... && result[4]@ == 4`.
#[test]
#[timeout(30000)]
fn test_flat_5_push_back_chain_reconstruction_postconditions() {
    let mut encoder = AYEncoder::new();

    // Build the flat requires pattern matching the actual e2e create_arr output.
    let mut all_requires = vec![eq(method_call(view(var("call_1")), "len", vec![]), int(0))];
    for val in 0..=4 {
        all_requires.push(eq(
            view(final_expr(var("call_1"))),
            method_call(view(var("call_1")), "push_back", vec![int(val)]),
        ));
    }
    encoder.register_sort_hints(&all_requires);

    // Encode and assert all requires with len-zero synthesis.
    for req in &all_requires {
        let term = encoder.encode_pure(req).expect("encode req");
        encoder.assert_term(term);
        encoder
            .try_synthesize_len_zero_seq_value(req, None)
            .expect("len==0 synthesis should not fail");
    }

    // Chain reconstruction: the key operation.
    encoder
        .try_reconstruct_flat_push_back_chain(&all_requires, None)
        .expect("flat push_back chain reconstruction should not fail");

    // Verify the target variable has a SeqValue.
    let target_term = *encoder
        .vars_for_test()
        .get("final_call_1_view")
        .expect("final_call_1_view should exist");
    let sv = encoder
        .seq_state_for_test()
        .get_seq_value(&target_term)
        .expect("chain reconstruction should register SeqValue for final_call_1_view");
    let (sv_len, sv_arr) = (sv.len, sv.arr);

    // len == 5
    let five = encoder.solver.int_const(5);
    assert_negated_eq_unsat(&mut encoder, sv_len, five, "len==5");

    // result[i]@ == i for i in 0..5
    for i in 0..5i64 {
        let idx = encoder.solver.int_const(i);
        let sel = encoder.solver.select(sv_arr, idx);
        let expected = encoder.solver.int_const(i);
        assert_negated_eq_unsat(
            &mut encoder,
            sel,
            expected,
            &format!("select(arr,{i})=={i}"),
        );
    }
}

/// After flat push_back chain reconstruction, postcondition queries on the
/// target variable resolve via read-over-write (select on store chains).
///
/// 2-element case: chain reconstruction synthesizes `store(store(const_array(0), 0, 0), 1, 1)`.
#[test]
#[timeout(30000)]
fn test_flat_push_back_chain_reconstruction_postcondition_2_elements() {
    let mut encoder = AYEncoder::new();

    let all_requires = vec![
        eq(method_call(view(var("call_1")), "len", vec![]), int(0)),
        eq(
            view(final_expr(var("call_1"))),
            method_call(view(var("call_1")), "push_back", vec![int(0)]),
        ),
        eq(
            view(final_expr(var("call_1"))),
            method_call(view(var("call_1")), "push_back", vec![int(1)]),
        ),
    ];
    encoder.register_sort_hints(&all_requires);
    for req in &all_requires {
        let term = encoder.encode_pure(req).expect("encode req");
        encoder.assert_term(term);
        encoder
            .try_synthesize_len_zero_seq_value(req, None)
            .expect("len==0 synthesis should not fail");
    }
    encoder
        .try_reconstruct_flat_push_back_chain(&all_requires, None)
        .expect("flat push_back chain reconstruction should not fail");

    let target_term = *encoder
        .vars_for_test()
        .get("final_call_1_view")
        .expect("final_call_1_view should exist");
    let sv = encoder
        .seq_state_for_test()
        .get_seq_value(&target_term)
        .expect("chain reconstruction should register SeqValue");
    let (sv_len, sv_arr) = (sv.len, sv.arr);

    // len == 2
    let two = encoder.solver.int_const(2);
    assert_negated_eq_unsat(&mut encoder, sv_len, two, "len==2");

    // select(arr, 0) == 0
    let zero = encoder.solver.int_const(0);
    let sel0 = encoder.solver.select(sv_arr, zero);
    assert_negated_eq_unsat(&mut encoder, sel0, zero, "select(arr,0)==0");

    // select(arr, 1) == 1
    let one = encoder.solver.int_const(1);
    let sel1 = encoder.solver.select(sv_arr, one);
    assert_negated_eq_unsat(&mut encoder, sel1, one, "select(arr,1)==1");
}
