//@ expect: verify
//@ mechanism: control for program_ensures_after_loop_field_write_fact_meets_loop_exit_fact, with the postcondition the body meets: the field written with `x` is `x`.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
//@ xfail: the post-loop walk forgets a local a field write changes, so `result` is unbound and the check is `unknown (incomplete loop: no single post-loop return value)`; `unknown` at the campaign tip too. Following the write is a completeness gap, not a soundness one.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == x)]
pub fn prog(n: u32, x: u32) -> u32 {
    let mut t = (0u32, 0u32);
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    t.0 = x;
    t.0
}
