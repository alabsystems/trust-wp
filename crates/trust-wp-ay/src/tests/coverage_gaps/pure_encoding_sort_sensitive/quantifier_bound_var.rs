// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Quantifier-bound variable collapse ───────────────────────────────

/// old(i) for quantifier-bound `i` collapses to `i`. (#1122)
#[test]
#[timeout(30000)]
fn quantifier_bound_var_old_collapses() {
    let mut encoder = AYEncoder::new();

    let expr = forall("i", gt(old(var("i")), int(0)));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "forall i. old(i) > 0 should encode: {result:?}"
    );

    assert!(
        encoder.var_sort("old_i").is_none(),
        "quantifier-bound old(i) must not create old_i variable"
    );
}
