//@ expect: reject
//@ mechanism: the return sits INSIDE the loop, so the exit the postcondition is checked at is a block of the loop itself; the exit-reachability query must still report the parameter
//@ accept-means: `f` returns 7, so `result@ == 0` is FALSE.
//@ fixed-by: wp-s59 loop-invalidated parameter facts in the ensures lane
//@ teeth: NO TEETH GAINED — already refused on wp-campaign 03a35447 (verdict `unknown`, A/B 2026-09-14). Kept as a regression guard for the exit-inside-the-loop shape.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
#[ensures(result@ == 0)]
pub fn f(a: &mut u32, n: u32) -> u32 {
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n {
        *a = 7;
        if i == 1 { return *a; }
        i += 1;
    }
    *a
}
