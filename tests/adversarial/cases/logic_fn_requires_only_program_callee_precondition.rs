//@ expect: reject
//@ mechanism: the requires-only spelling of logic_fn_program_callee_precondition: the function is credited on its body goals, the body calls a program function, and the call is refused rather than read as a placeholder (D-136).
//@ accept-means: a requires-only logic function that calls a program function outside its precondition is credited `verified` on a true assertion.
//@ WHY IT IS FALSE: at `y == 0` the body calls `prog(0)`, and `prog` requires `x@ > 0`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `prog verified ✓` and the assertion `proved, not credited`; the call was never examined, and the crate's clean exit stood on `prog` alone.
//@ fixed-by: D-119
//@ verdict: unknown
//@ refused-with: which the logic lane does not read
//@ also-verified: prog
//@ also-verified-assertion: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ > 0)]
#[ensures(result == x)]
pub fn prog(x: i32) -> i32 {
    x
}

#[logic]
#[requires(true)]
pub fn caller(y: i32) -> i32 {
    proof_assert!(true);
    prog(y)
}
