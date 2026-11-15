//@ expect: reject
//@ mechanism: a logic function whose contract is a `#[requires]` alone still gets a `vc_` goal in Creusot (`translate_logic` returns early only for an EMPTY contract), and the body's assertion is part of it. trust-wp's logic lane skipped every logic function with no `ensures`, so this body was never looked at.
//@ accept-means: a contracted logic function's own assertion, false for most arguments its precondition admits, is never examined, and the crate exits 0 on the one function that was (`zero`, TRUE, beside it so that the run examines something).
//@ WHY THE ASSERTION IS FALSE: `x == 1` satisfies `x > 0` and not `x > 5`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `f is a logic function (definition registered)` and `creusot_test::zero verified ✓`. Without `zero` the run examines nothing and exits 2, which is why it is there.
//@ fixed-by: D-106
//@ fn-failed: creusot_test::f
//@ also-verified: creusot_test::zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn f(x: Int) -> Int {
    proof_assert!(x > 5);
    x
}

#[logic]
#[ensures(result == 0)]
pub fn zero() -> Int {
    0
}
