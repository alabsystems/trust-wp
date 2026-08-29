// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Verify: NOT(exists<a:Bool> a) ≡ forall<a:Bool> NOT a
#[test]
#[timeout(30000)]
fn de_morgan_single_existential_equivalence() {
    let original = exists_with_sort("a", ExprSort::Bool, var("a"));
    // Manual De Morgan: forall<a> NOT a
    let de_morgan = forall_with_sort("a", ExprSort::Bool, not(var("a")));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "single existential De Morgan must be semantically equivalent"
    );
}

/// Verify: NOT(exists<a> exists<b> (a AND b)) ≡ forall<a> forall<b> NOT(a AND b)
#[test]
#[timeout(30000)]
fn de_morgan_nested_existentials_equivalence() {
    let original = exists_with_sort(
        "a",
        ExprSort::Bool,
        exists_with_sort("b", ExprSort::Bool, and(var("a"), var("b"))),
    );
    let de_morgan = forall_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort("b", ExprSort::Bool, not(and(var("a"), var("b")))),
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "nested existential De Morgan must be semantically equivalent"
    );
}

/// Verify: NOT(exists<a> exists<b> exists<c> (a AND b AND c))
///       ≡ forall<a> forall<b> forall<c> NOT(a AND b AND c)
#[test]
#[timeout(30000)]
fn de_morgan_triple_nested_existentials_equivalence() {
    let body = and(and(var("a"), var("b")), var("c"));
    let original = exists_with_sort(
        "a",
        ExprSort::Bool,
        exists_with_sort(
            "b",
            ExprSort::Bool,
            exists_with_sort("c", ExprSort::Bool, body.clone()),
        ),
    );
    let de_morgan = forall_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort(
            "b",
            ExprSort::Bool,
            forall_with_sort("c", ExprSort::Bool, not(body)),
        ),
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "triple nested De Morgan must be semantically equivalent"
    );
}

/// Verify: NOT(exists<a> forall<b> (a == b)) ≡ forall<a> NOT(forall<b> (a == b))
///
/// Mixed quantifier nesting: only the outermost exists is rewritten.
/// The inner forall's negation is handled at the ay level.
#[test]
#[timeout(30000)]
fn de_morgan_mixed_exists_forall_equivalence() {
    let inner = forall_with_sort("b", ExprSort::Bool, binop(var("a"), BinOp::Eq, var("b")));
    let original = exists_with_sort("a", ExprSort::Bool, inner.clone());
    let de_morgan = forall_with_sort("a", ExprSort::Bool, not(inner));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "mixed exists/forall De Morgan must be semantically equivalent"
    );
}

/// Verify: NOT(exists<a> exists<b> forall<c> (a AND b AND c))
///       ≡ forall<a> forall<b> NOT(forall<c> (a AND b AND c))
///
/// Exercises the exists-exists-forall alternation pattern. The recursive
/// `negate_existential_postcondition` pushes through consecutive existentials
/// (a, b) and stops at the forall(c), leaving it negated at ay level.
#[test]
#[timeout(30000)]
fn de_morgan_exists_exists_forall_alternation() {
    let body = and(and(var("a"), var("b")), var("c"));
    let original = exists_with_sort(
        "a",
        ExprSort::Bool,
        exists_with_sort(
            "b",
            ExprSort::Bool,
            forall_with_sort("c", ExprSort::Bool, body.clone()),
        ),
    );
    // After De Morgan: forall<a> forall<b> NOT(forall<c> (a AND b AND c))
    let de_morgan = forall_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort(
            "b",
            ExprSort::Bool,
            not(forall_with_sort("c", ExprSort::Bool, body)),
        ),
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "exists-exists-forall alternation De Morgan must be semantically equivalent"
    );
}

/// Verify De Morgan preservation through the actual encoder pipeline.
///
/// Encode both `NOT(exists<a:Bool> a)` and `forall<a:Bool> NOT a` through
/// `encode_pure`, then check they produce the same solver result when
/// asserted. This tests the full pipeline including any trigger synthesis
/// or sort inference that the encoder applies.
#[test]
#[timeout(30000)]
fn de_morgan_through_encoder_pipeline() {
    // Direct negation of exists via ay-level NOT
    let original = exists_with_sort("a", ExprSort::Bool, var("a"));
    let negated = not(original);

    // De Morgan form via PureExpr-level rewrite
    let de_morgan = forall_with_sort("a", ExprSort::Bool, not(var("a")));

    // Encode both and check they're equivalent
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let equivalence = binop(negated, BinOp::Eq, de_morgan);
    let violates = not(equivalence);
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "encoder pipeline should produce equivalent results for both forms"
    );
}
