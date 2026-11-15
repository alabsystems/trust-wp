//@ expect: reject
//@ mechanism: the charge the assumption-position division rule of D-118 must not lose: a BODY
//@ mechanism: division or remainder whose result is bound to a local and never returned, so the
//@ mechanism: operation appears only in the facts the extractor assumes, in straight-line code and
//@ mechanism: in a loop body. The rule drops the encoder's `divisor != 0` from assumptions because
//@ mechanism: the MIR `Assert(DivisionByZero | RemainderByZero)` owns it; this case holds it to that.
//@ accept-means: `hop(1, 0)`, `hop_rem(1, 0)` or `hop_in_loop(1, 0)` divides by zero and is credited.
//@ fixed-by: D-118
//@ teeth: every host refuted before and after D-118.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 1)]
pub fn hop(a: u32, b: u32) -> u32 {
    let _q = a / b;
    1
}

#[ensures(result@ == 1)]
pub fn hop_rem(a: u32, b: u32) -> u32 {
    let _r = a % b;
    1
}

#[ensures(result@ == 1)]
pub fn hop_in_loop(n: u32, b: u32) -> u32 {
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n {
        let _q = i / b;
        i += 1;
    }
    1
}
