// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Let binding encoding ─────────────────────────────────────────────

/// let x = 5 in x > 0 is equivalent to true.
#[test]
#[timeout(30000)]
fn let_binding_substitution_semantic() {
    let mut encoder = AYEncoder::new();

    let expr = let_bind("x", int(5), gt(var("x"), int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("let binding should encode");

    let neg = encoder.solver.not(term);
    encoder.solver.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(let x=5 in x>0) must be UNSAT"
    );
}
