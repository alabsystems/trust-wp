//@ expect: verify
//@ mechanism: control for program_ensures_after_loop_call_read_as_its_argument, with the postcondition the body meets: `succ(i)` is `n + 1`.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
//@ xfail: the post-loop walk gives no value for a call's result, so `result` is unbound and the check is `unknown (incomplete loop: no single post-loop return value)`; FAILED with a counterexample at the campaign tip, where the walk read `succ(i)` as `i`. Reading the call through its contract here is a completeness gap, not a soundness one.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x < 100)]
#[ensures(result == x + 1)]
pub fn succ(x: u32) -> u32 {
    x + 1
}

#[requires(n < 100)]
#[ensures(result == n + 1)]
pub fn prog(n: u32) -> u32 {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    succ(i)
}
