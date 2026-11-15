//@ expect: reject
//@ mechanism: the loop writes the parameter's pointee only on one branch; a MAY-write is still enough to invalidate the entry fact
//@ accept-means: for `c == true`, `f` returns 7, so `result@ == 0` is FALSE.
//@ fixed-by: wp-s59 loop-invalidated parameter facts in the ensures lane
//@ teeth: verified ✓ (exit 0) on wp-campaign 03a35447 — the ensures lane discharged the false postcondition from the stale entry fact (A/B over an adversarial corpus run)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
#[ensures(result@ == 0)]
pub fn f(a: &mut u32, c: bool) -> u32 {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { if c { *a = 7; } i += 1; }
    *a
}
