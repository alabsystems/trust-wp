//@ expect: verify
//@ mechanism: control for loop_lane_result_early_return_before_loop: the early return gives 0, so
//@ mechanism: `ensures(result == 0u32)` is TRUE on both paths.
//@ xfail: no loop every return passes through states the returned value (D-224), so `result` is unbound
//@ xfail: (D-165) and the postcondition is not proved. It verified on this branch over the primary walk's
//@ xfail: result merging the two returns, which D-165 does not let stand in after a loop.
//@ xfail-verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn f(c: bool, n: u32) -> u32 {
    if c {
        return 0;
    }
    let mut i = 0u32;
    let k = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    k
}
