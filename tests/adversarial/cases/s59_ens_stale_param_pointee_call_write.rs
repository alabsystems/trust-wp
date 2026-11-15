//@ expect: reject
//@ mechanism: the loop writes the parameter's pointee through a CALL (`set(a)`); the entry fact about `*a` still discharged the postcondition
//@ accept-means: for `n > 0`, `f` returns 7, so `result@ == 0` is FALSE.
//@ fixed-by: wp-s59 loop-invalidated parameter facts in the ensures lane
//@ teeth: verified ✓ (exit 0) on wp-campaign 03a35447 — the ensures lane discharged the false postcondition from the stale entry fact (A/B'd in a full adversarial run against the post-fix build)
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures((^x)@ == 7)]
pub fn set(x: &mut u32) { *x = 7; }

#[requires((*a)@ == 0)]
#[ensures(result@ == 0)]
pub fn f(a: &mut u32, n: u32) -> u32 {
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n { set(a); i += 1; }
    *a
}
