//@ expect: verify
//@ mechanism: control for loop_condition_call_one_sided_exit: the same loop under the TRUE
//@ mechanism: `ensures(result <= n)`. Preservation needs `pos`'s one-sided clause at the evaluation
//@ mechanism: that entered the body (`i > 0`, so `i -= 1` does not underflow); the exit needs only the
//@ mechanism: invariant. It was a validated `FAILED (loop invariant)` before D-222, where the
//@ mechanism: condition read a placeholder no clause described: a refutation of a true program.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result ==> k > 0u32)]
pub fn pos(k: u32) -> bool { k > 3 }

#[requires(n < 50u32)]
#[ensures(result <= n)]
pub fn h(n: u32) -> u32 {
    let mut i = n;
    #[invariant(i <= n)]
    while pos(i) { i -= 1; }
    i
}
