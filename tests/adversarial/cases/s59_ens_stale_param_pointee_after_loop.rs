//@ expect: reject
//@ mechanism: the `#[requires]` fact about the ENTRY pointee survived a loop that writes `*a`; the encoder names both values `a_current`, so the ENSURES lane discharged a false postcondition
//@ accept-means: `f` returns 7, so `result@ == 0` is FALSE; it is discharged only by the stale entry fact `(*a)@ == 0` fused with the loop's `*a = 7` write.
//@ fixed-by: wp-s59 loop-invalidated parameter facts in the ensures lane
//@ teeth: verified ✓ (exit 0) on wp-campaign 03a35447 — the ensures lane discharged the false postcondition from the stale entry fact (adversarial run, A/B'd against the changed build)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
#[ensures(result@ == 0)]
pub fn f(a: &mut u32) -> u32 {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { *a = 7; i += 1; }
    *a
}
