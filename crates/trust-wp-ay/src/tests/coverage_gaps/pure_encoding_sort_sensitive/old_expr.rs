// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Old expression encoding ──────────────────────────────────────────

/// old(x) prefixes the variable name with "old_".
#[test]
#[timeout(30000)]
fn old_var_creates_prefixed_variable() {
    let mut encoder = AYEncoder::new();

    let expr = old(var("x"));
    let _term = encoder.encode_pure(&expr).expect("old(x) should encode");

    assert!(
        encoder.var_sort("old_x").is_some(),
        "old(var(x)) must create a variable named old_x"
    );
}

/// old(*v) is identity — *v represents entry-state in RustHorn.
#[test]
#[timeout(30000)]
fn old_deref_is_identity() {
    let mut encoder = AYEncoder::new();

    let deref_expr = deref(var("v"));
    let term1 = encoder.encode_pure(&deref_expr).expect("*v should encode");

    let old_deref_expr = old(deref(var("v")));
    let term2 = encoder
        .encode_pure(&old_deref_expr)
        .expect("old(*v) should encode");

    let neq = encoder.solver.neq(term1, term2);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "*v != old(*v) must be UNSAT — old(*v) is identity for deref"
    );
}
