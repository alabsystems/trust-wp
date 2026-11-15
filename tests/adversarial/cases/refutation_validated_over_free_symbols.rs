//@ expect: verify
//@ xfail: spec-level `/` and `%` on integer views are not evaluated at concrete operands, so every true quotient claim is refuted
//@ mechanism: a refutation published as validated against a goal its own printed model does not falsify — spec-level `/` and `%` on integer views are carried as free terms, so ay answers sat with a model that pins BOTH operands and still "refutes" the quotient
//@ fixed-by: ?
//@ accept-means: n/a (control) — every claim below is true for the operands its own precondition pins; a clean verify is the signal that spec-level division stopped being a free term
//@ teeth: quotient_ge and quotient_le are exhaustive — for any integer value of the term at least one of `>= 2` and `<= 2` holds — yet both are refuted with the identical counterexample `l = 6, r = 3`, so at least one refutation is published against a goal its model does not falsify; product_eq and sum_eq are the same shape on `*` and `+` and verify today, which rules out a broken view-to-parameter link and localises the defect to `/` and `%`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// The precondition pins both operands, so the quotient term has exactly one
// value. Refuting this claim requires a model in which `6 / 3` is not 2.
#[requires(l@ == 6)]
#[requires(r@ == 3)]
#[ensures(l@ / r@ == 2)]
pub fn quotient_eq(l: i8, r: i8) {
    let _ = (l, r);
}

// quotient_ge and quotient_le cannot both be false: whatever integer the term
// denotes is either at least 2 or at most 2. Any model refuting one satisfies
// the other, so a shared counterexample is an invalid model, not a refutation.
#[requires(l@ == 6)]
#[requires(r@ == 3)]
#[ensures(l@ / r@ >= 2)]
pub fn quotient_ge(l: i8, r: i8) {
    let _ = (l, r);
}

#[requires(l@ == 6)]
#[requires(r@ == 3)]
#[ensures(l@ / r@ <= 2)]
pub fn quotient_le(l: i8, r: i8) {
    let _ = (l, r);
}

// `%` rides the same encoding as `/`.
#[requires(l@ == 7)]
#[requires(r@ == 3)]
#[ensures(l@ % r@ == 1)]
pub fn remainder_eq(l: i8, r: i8) {
    let _ = (l, r);
}

// Contrast, and the reason this is not a view-linking failure: the identical
// shape over `*` and `+` is discharged from the same two preconditions.
#[requires(l@ == 6)]
#[requires(r@ == 3)]
#[ensures(l@ * r@ == 18)]
pub fn product_eq(l: i8, r: i8) {
    let _ = (l, r);
}

#[requires(l@ == 6)]
#[requires(r@ == 3)]
#[ensures(l@ + r@ == 9)]
pub fn sum_eq(l: i8, r: i8) {
    let _ = (l, r);
}

// The corpus shape. The range precondition admits no overflowing input:
// `-128 / -1` is 128, which `<= 127` excludes, so the division cannot panic
// and the postcondition holds by the body. It is refuted on the raw operands.
#[requires(r@ != 0)]
#[requires(l@ / r@ >= -128 && l@ / r@ <= 127)]
#[ensures(result@ == l@ / r@)]
pub fn test_div(l: i8, r: i8) -> i8 {
    l / r
}
