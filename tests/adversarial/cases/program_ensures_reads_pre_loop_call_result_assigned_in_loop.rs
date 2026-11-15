//@ expect: reject
//@ mechanism: `let mut k = zero()` (`ensures(result == 0u32)`) before an annotated loop whose body assigns
//@ mechanism: `k = 5`; the function returns `k` and claims `result == 0u32`. The loop lane finds the
//@ mechanism: counterexample and defers to the function-level path ("postcondition deferred to function-level
//@ mechanism: path"), which reads `result` as the name `k` after the loop and keeps `zero`'s postcondition about
//@ mechanism: that same name, stated by the block-slice walker before the loop, as a premise. The loop's write
//@ mechanism: to `k` does not retire it.
//@ accept-means: a function that returns 5 is credited with a postcondition saying it returns 0, and the crate
//@ accept-means: exits 0.
//@ WHY IT IS FALSE: `go()` returns 5: the loop runs three times and assigns `k = 5` on each pass.
//@ teeth: MEASURED ACCEPTED, exit 0, at the wp-campaign tip and with D-235 (`trust-wp: zero verified ✓`,
//@ teeth: `trust-wp: go verified ✓` after `postcondition deferred to function-level path`). With `k = 0u32`
//@ teeth: or a contract-free `zero()` in place of the call, `go` is FAILED (postcondition): the premise is the
//@ teeth: call's postcondition.
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
    #[invariant(m <= 3u32)]
    while m < 3 {
        k = 5;
        m += 1;
    }
    k
}
