//@ expect: reject
//@ mechanism: after a first annotated loop, `let mut k = zero()` (`ensures(result == 0u32)`), `let r = &mut k`, and a
//@ mechanism: second annotated loop writes `*r = 5`; the function returns `k` and claims `result == 0u32`. The
//@ mechanism: block-slice walker states `zero`'s postcondition about the bare name `k`
//@ mechanism: (`collect_call_effects_for_blocks`): D-235's `PastLoopNames::destination_names_only_this_result`
//@ mechanism: lets the call through because the only other change of `k` is a borrow after the call, which it
//@ mechanism: reads as lending the result on without binding the name to another value. The second loop writes
//@ mechanism: through that loan, so after it `k` is 5; the loop lane withholds its refutation ("the loop VC does
//@ mechanism: not determine `k` after the loop") and defers to the function-level path, which reads `result` as
//@ mechanism: the same name `k` and takes `k == 0` from the postcondition.
//@ accept-means: a function that returns 5 is credited with a postcondition saying it returns 0, and the crate
//@ accept-means: exits 0.
//@ WHY IT IS FALSE: `go()` returns 5: the second loop runs three times and each pass stores 5 through `r`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the wp-campaign tip and with D-235 (`trust-wp: zero verified ✓`,
//@ teeth: `trust-wp: go verified ✓`), and with D-235's post-loop call gate disabled. Without the second
//@ teeth: loop (`*r = 5` straight-line, or a callee handed `r`) `go` is `unknown`; the same shape storing `k`
//@ teeth: through an `&mut` out-parameter is ACCEPTED as well.
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
    let mut n = 0u32;
    let mut m = 0u32;
    #[invariant(n <= 3u32)]
    while n < 3 {
        n += 1;
    }
    let mut k = zero();
    let r = &mut k;
    #[invariant(m <= 3u32)]
    while m < 3 {
        *r = 5;
        m += 1;
    }
    k
}
