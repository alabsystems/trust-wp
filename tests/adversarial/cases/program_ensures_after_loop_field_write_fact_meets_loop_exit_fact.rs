//@ expect: reject
//@ mechanism: a program function builds a tuple `(0, 0)`, runs an annotated loop, writes its input `x` into the first field and returns that field, claiming `result == 0`. Two readings accept it. At the campaign tip the post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`) does not see the field write and reads the tuple at its value from before the loop (program_ensures_after_loop_field_write_read_as_stale_field.rs). With the walk giving no value for a local it cannot follow, the function-level check (`callbacks::verification::per_contract`) read `result` from the whole-body extraction, which states the write as the fact `t.0 == x` about the local `t`, while the loop-exit facts state `t == (0, 0)` about the same name at the loop's exit: together they prove `x == 0`, a premise that is consistent and false (measured ACCEPTED at an intermediate head of the fix). With the write `t.0 = 7` the two facts contradict, and the vacuity check refuses the crate.
//@ fixed-by: D-165
//@ accept-means: a function that returns its input is credited with a postcondition saying it returns `0`, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, 1)` returns `1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog unknown (timeout)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
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
