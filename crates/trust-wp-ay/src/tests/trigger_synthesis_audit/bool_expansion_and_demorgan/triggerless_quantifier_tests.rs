// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Degenerate case: triggerless quantifier with literal-only body.
/// `forall<i> true` — no function calls, no variable references.
/// Trigger synthesis should return empty, encoder should handle gracefully.
#[test]
#[timeout(30000)]
fn triggerless_quantifier_with_literal_body() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<i> true — trivially true, but synthesis has nothing to work with
    let expr = forall("i", PureExpr::Bool(true));
    let term = encoder
        .encode_pure(&expr)
        .expect("literal-body quantifier should encode without panic");
    assert_synthesized_triggers(&encoder, &[]);
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        result != SolveResult::unsat(),
        "forall<i> true should be satisfiable, got {:?}",
        result
    );
}

/// `forall<i> false` — negative companion to `triggerless_quantifier_with_literal_body`.
///
/// Unlike `forall<i> true` (which is trivially satisfiable and cannot distinguish
/// a working encoder from one that drops quantifiers), `forall<i> false` is always
/// unsatisfiable. If the encoder incorrectly dropped the quantifier, it would
/// return Sat/Unknown instead of Unsat, catching that class of bugs.
///
/// Re: #1107 (weak assertions in trigger synthesis tests)
#[test]
#[timeout(30000)]
fn triggerless_quantifier_with_false_body_must_be_unsat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // forall<i> false — always false, so asserting it should produce Unsat
    let expr = forall("i", PureExpr::Bool(false));
    let term = encoder
        .encode_pure(&expr)
        .expect("literal-false-body quantifier should encode without panic");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "forall<i> false is unsatisfiable — if this returns Sat/Unknown, \
         the encoder may be dropping quantifiers or mishandling literal bodies: {result:?}"
    );
}
