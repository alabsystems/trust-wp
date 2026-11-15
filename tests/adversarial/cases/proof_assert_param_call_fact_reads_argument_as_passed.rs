//@ expect: reject
//@ mechanism: regression guard for the by-value parameter entry/current versioning (D-241): a callee's
//@ mechanism: postcondition is stated over its argument as the body passed it (`$call > x + 1` after
//@ mechanism: `x = x + 1`, in the entry value's terms), and the lane substituted the parameter's
//@ mechanism: binding at the assertion into it a second time (`$call > (x + 1) + 1`). Keeping the
//@ mechanism: re-bound parameter's `#[requires]` as an entry fact (which discharges the callee's
//@ mechanism: `a@ < 100` guard) without renaming the parameter inside the callee's fact would prove
//@ mechanism: the FALSE claim below from the doubled fact.
//@ accept-means: a callee's postcondition about an argument that read a re-bound parameter is applied
//@ accept-means: to the parameter's later binding a second time.
//@ WHY THE CONTRACT IS FALSE: `double_applied(0)` passes 1 to `grow`, which may return 2; the claim is
//@ WHY THE CONTRACT IS FALSE: `2 > 2`.
//@ fixed-by: D-241: the parameter's own name inside the callee's fact is its entry symbol, which the
//@ fixed-by: substitution of its binding at the assertion does not reach.
//@ teeth: on D-240 the assertion is `unknown` only because the substitution fact `x == x + 1` makes
//@ teeth: the premises contradictory (the vacuity guard); FAILED with D-241.
//@ also-verified: grow
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@ < 100)]
#[ensures(result@ > a@)]
pub fn grow(a: u32) -> u32 {
    a + 1
}

#[requires(x@ < 10)]
pub fn double_applied(mut x: u32) {
    x = x + 1;
    let r = grow(x);
    proof_assert!(r@ > x@ + 1);
}
