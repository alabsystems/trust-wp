// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Seq Ne no-propagation (#1810) ────────────────────────────────────

/// BinOp::Ne with Seq operands must NOT propagate SeqValue from source to target.
/// (#1810): propagation on Ne creates a false association — the target gets
/// source's SeqValue components, but the decomposed term only says they DIFFER.
///
/// Semantic: after encoding `s != t`, subsequent `t.len()` must NOT use
/// s's concrete SeqValue (which would make len(t) = len(s), defeating the Ne).
#[test]
#[timeout(30000)]
fn seq_ne_does_not_propagate_seq_value() {
    let mut encoder = AYEncoder::new();

    // Assert s != t — Ne decomposition, but NO propagation
    let ne_expr = ne(
        method_call(
            logic_fn_call("seq_empty", vec![]),
            "push_back",
            vec![int(10)],
        ),
        var_with_sort("t", ExprSort::Seq),
    );
    let ne_term = encoder.encode_pure(&ne_expr).expect("Seq Ne should encode");

    // Structural: t should NOT have a SeqValue — Ne path must not propagate.
    // This is the key invariant this test covers (#1810).
    let t_term = encoder
        .encode_pure(&var_with_sort("t", ExprSort::Seq))
        .expect("t should encode");
    assert!(
        !encoder.seq_state_for_test().has_seq_value(&t_term),
        "Ne must NOT propagate SeqValue to target (#1810)"
    );

    // Solver-level SAT verification (t.len()!=1 with s!=t should be SAT)
    // is blocked by ay-dpll Array theory performance regression (#2594).
    let _ = ne_term;
}
