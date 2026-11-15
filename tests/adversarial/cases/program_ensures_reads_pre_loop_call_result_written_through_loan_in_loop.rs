//@ expect: reject
//@ mechanism: `let mut k = zero()` (`ensures(result == 0u32)`) and `let r = &mut k` before an annotated loop
//@ mechanism: whose body writes `*r = 5`; the function returns `k` and claims `result == 0u32`. The loop lane
//@ mechanism: withholds its refutation ("the loop VC does not determine `k` after the loop") and defers to the
//@ mechanism: function-level path, which reads `result` as the name `k` and keeps `zero`'s postcondition about
//@ mechanism: that same name, stated by the block-slice walker before the loop, as a premise.
//@ mechanism: program_ensures_reads_pre_loop_call_result_assigned_in_loop.rs is the spelling with a direct write.
//@ accept-means: a function that returns 5 is credited with a postcondition saying it returns 0, and the crate
//@ accept-means: exits 0.
//@ WHY IT IS FALSE: `go()` returns 5: the loop runs three times and stores 5 through `r` on each pass.
//@ teeth: MEASURED ACCEPTED, exit 0, at the wp-campaign tip and with D-235 (`trust-wp: zero verified ✓`,
//@ teeth: `trust-wp: go verified ✓`). With `k = 0u32` in place of the call, `go` is `unknown`.
//@ also-verified: zero
//@ fixed-by: D-243 (a call's postcondition is not a premise of a slice that runs after a later loop that may change a name it speaks of, directly or through a loan).
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn zero() -> u32 {
    0
}

#[ensures(result == 0u32)]
pub fn go() -> u32 {
    let mut m = 0u32;
    let mut k = zero();
    let r = &mut k;
    #[invariant(m <= 3u32)]
    while m < 3 {
        *r = 5;
        m += 1;
    }
    k
}
