// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── Seq-receiver UF fallback tests (#1667) ─────────────────────────
//
// Seq does not define `remove`, `intersection`, or `difference`.
// When a Seq-hinted receiver calls these methods, method_call/mod.rs
// falls through to `encode_int_method_uf`
// instead of `encode_fset_method`. These tests verify that path.

/// `remove` on a Seq-hinted receiver falls through to Int UF,
/// not FSet remove (method_call/mod.rs).
#[test]
#[timeout(30000)]
fn test_seq_receiver_remove_falls_to_int_uf() {
    let mut encoder = AYEncoder::new();

    // Establish Seq sort hint for v_view via push_back scan
    let hint = method_call(view(var("v")), "push_back", vec![int(1)]);
    encoder.register_sort_hints(std::slice::from_ref(&hint));

    // Call remove on the Seq-hinted receiver
    let expr = method_call(view(var("v")), "remove", vec![int(3)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Seq.remove should fall through to Int UF");

    // Must NOT use FSet remove
    assert!(
        !encoder.decls().has_spec_func("fset_remove"),
        "Seq.remove should NOT route to FSet; found spec_functions: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );

    // Should declare an Int-returning method UF.
    // Receiver is Seq-sorted (uninterpreted "u"), arg is Int ("i").
    let has_uf = encoder
        .decls()
        .logic_func_names()
        .any(|k| k.starts_with("method_remove_"));
    assert!(
        has_uf,
        "Seq.remove should declare method_remove_* UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );

    // Semantic: result participates in Int constraints
    let five = encoder.solver.int_const(5);
    let eq5 = encoder.solver.eq(term, five);
    encoder.assert_term(eq5);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Seq.remove UF == 5 should be SAT, got {result:?}"
    );
}

/// `intersection` on a Seq-hinted receiver falls through to Int UF,
/// not FSet intersection (method_call/mod.rs).
#[test]
#[timeout(30000)]
fn test_seq_receiver_intersection_falls_to_int_uf() {
    let mut encoder = AYEncoder::new();

    // Establish Seq sort hint for v_view
    let hint = method_call(view(var("v")), "push_back", vec![int(1)]);
    encoder.register_sort_hints(std::slice::from_ref(&hint));

    let expr = method_call(view(var("v")), "intersection", vec![view(var("w"))]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Seq.intersection should fall through to Int UF");

    // Must NOT use FSet intersection
    assert!(
        !encoder.decls().has_spec_func("fset_intersection"),
        "Seq.intersection should NOT route to FSet; found spec_functions: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );

    // Should declare a method_intersection_* UF
    let has_uf = encoder
        .decls()
        .logic_func_names()
        .any(|k| k.starts_with("method_intersection_"));
    assert!(
        has_uf,
        "Seq.intersection should declare method_intersection_* UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );

    // Functional equality: same inputs produce same output
    let term2 = encoder
        .encode_pure(&method_call(
            view(var("v")),
            "intersection",
            vec![view(var("w"))],
        ))
        .expect("second intersection encode");
    let neq = encoder.solver.neq(term, term2);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "identical intersection UF applications must be equal"
    );
}

/// `difference` on a Seq-hinted receiver falls through to Int UF,
/// not FSet difference (method_call/mod.rs).
#[test]
#[timeout(30000)]
fn test_seq_receiver_difference_falls_to_int_uf() {
    let mut encoder = AYEncoder::new();

    // Establish Seq sort hint for v_view
    let hint = method_call(view(var("v")), "push_back", vec![int(1)]);
    encoder.register_sort_hints(std::slice::from_ref(&hint));

    let expr = method_call(view(var("v")), "difference", vec![view(var("w"))]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Seq.difference should fall through to Int UF");

    // Must NOT use FSet difference
    assert!(
        !encoder.decls().has_spec_func("fset_difference"),
        "Seq.difference should NOT route to FSet; found spec_functions: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );

    // Should declare a method_difference_* UF
    let has_uf = encoder
        .decls()
        .logic_func_names()
        .any(|k| k.starts_with("method_difference_"));
    assert!(
        has_uf,
        "Seq.difference should declare method_difference_* UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );

    // Functional equality: same inputs produce same output
    let term2 = encoder
        .encode_pure(&method_call(
            view(var("v")),
            "difference",
            vec![view(var("w"))],
        ))
        .expect("second difference encode");
    let neq = encoder.solver.neq(term, term2);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "identical difference UF applications must be equal"
    );
}
