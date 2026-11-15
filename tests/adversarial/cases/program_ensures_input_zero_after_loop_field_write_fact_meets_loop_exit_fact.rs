//@ expect: reject
//@ mechanism: the spelling of program_ensures_after_loop_field_write_fact_meets_loop_exit_fact.rs whose postcondition never mentions `result`: a program function builds a tuple `(0, 0)`, runs an annotated loop, writes its input `x` into the first field, returns that field and claims `x == 0`. When the post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`) gives no value, the whole-body extraction's return expression carried the write as the fact `t.0 == x` into the function-level check, beside the loop-exit fact `t == (0, 0)`: together they prove `x == 0`. Leaving `result` unbound only for a postcondition that mentions it kept the facts for this one.
//@ fixed-by: D-165
//@ accept-means: a function is credited with a postcondition about its argument that nothing requires, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, 1)` is a call with `x == 1`.
//@ teeth: MEASURED at the campaign tip: `trust-wp: prog unknown (timeout)` (the walk read the tuple from before the write and stated nothing about `x`). MEASURED ACCEPTED, exit 0, at an intermediate head of D-165 that dropped the whole-body extraction only for a postcondition mentioning `result`: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog unknown (timeout)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x == 0u32)]
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
