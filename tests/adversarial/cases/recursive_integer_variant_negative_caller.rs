//@ expect: reject
//@ verdict: failed
//@ fn-failed: countdown
//@ mechanism: the mathematical variant n@ must be nonnegative at every recursive caller; strict decrease alone misses the caller n=-1.
//@ accept-means: an invalid mathematical-integer well-founded relation is credited with termination.
//@ fixed-by: D-259; recursive_verify::bounded_integer_decrease makes the caller lower bound a goal.
// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n@)]
pub fn countdown(n: i32) -> i32 {
    if n >= -1 { countdown(n - 1) } else { 0 }
}
