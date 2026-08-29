// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── Semantic trigger-synthesis integration tests ─────────────────────
//
// Unlike the encode-only tests above, these tests call `check_sat()` and
// assert a concrete outcome. This proves that trigger synthesis produces
// usable triggers that make ay E-matching succeed. A formula that returns
// Unknown without triggers should return Sat/Unsat with synthesized triggers.
// Without trigger synthesis, the `assert!` would fail because ay's auto-
// extraction returns Unknown. Re: P1-373 audit.

/// Semantic test: triggerless forall contradiction becomes UNSAT via synthesis.
///
/// `forall<i> test_f(i) > 0` with `test_f(a) = -1` asserted as ground fact.
/// Without triggers: ay returns Unknown (cannot instantiate).
/// With synthesized trigger `{:pattern test_f(i)}`: ay instantiates at `a`
/// and discovers the contradiction `test_f(a) = -1 > 0` is false.
#[test]
#[timeout(30000)]
fn test_triggerless_synthesis_enables_unsat_detection() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function f: Int -> Int, body: x + 1
    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::test::test_f".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    );
    encoder
        .register_logic_fn(&f_def)
        .expect("register logic fn");

    // Ground fact: test_f(a) = -1 (assert via encode_pure)
    let ground = eq(logic_fn_call("test_f", vec![var("a")]), int(-1));
    let ground_term = encoder.encode_pure(&ground).expect("encode ground fact");
    encoder.assert_term(ground_term);

    // Quantified assertion: forall<i> test_f(i) > 0
    // No user triggers — synthesis should fire and pick {:pattern test_f(i)}
    let quantified = forall("i", gt(logic_fn_call("test_f", vec![var("i")]), int(0)));
    let q_term = encoder.encode_pure(&quantified).expect("encode quantified");
    encoder.assert_term(q_term);

    // With synthesized trigger, ay instantiates forall at `a` and finds:
    //   test_f(a) = -1 AND test_f(a) > 0 → contradiction → UNSAT
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "triggerless forall with synthesized trigger should detect contradiction"
    );
}

/// Semantic test: triggerless multi-var forall contradiction is UNSAT via synthesis.
///
/// `forall<i,j> test_g(i,j) > 0` with `test_g(a,b) = -5` asserted.
/// Tests that nested triggerless quantifier collapse + trigger synthesis
/// produce a usable multi-variable trigger `{:pattern test_g(i,j)}`.
#[test]
#[timeout(30000)]
fn test_triggerless_multi_var_synthesis_enables_unsat_detection() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register logic function g: (Int, Int) -> Int, body: a + b
    let g_def = LogicFnDef::new(
        "test_g".to_string(),
        "crate::test::test_g".to_string(),
        vec!["a".to_string(), "b".to_string()],
        add(var("a"), var("b")),
    );
    encoder
        .register_logic_fn(&g_def)
        .expect("register logic fn");

    // Ground fact: test_g(a, b) = -5
    let ground = eq(logic_fn_call("test_g", vec![var("a"), var("b")]), int(-5));
    let ground_term = encoder.encode_pure(&ground).expect("encode ground fact");
    encoder.assert_term(ground_term);

    // Quantified: forall<i> forall<j> test_g(i, j) > 0
    // Synthesis should collapse nested quantifiers and find {:pattern test_g(i,j)}
    let inner = forall(
        "j",
        gt(logic_fn_call("test_g", vec![var("i"), var("j")]), int(0)),
    );
    let expr = forall("i", inner);
    let q_term = encoder.encode_pure(&expr).expect("encode quantified");
    encoder.assert_term(q_term);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "triggerless multi-var forall with synthesized trigger should detect contradiction"
    );
}
