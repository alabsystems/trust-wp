//@ expect: reject
//@ mechanism: the entry fact names the pointee reached through a `Box` parameter; a loop writing `**b` leaves it standing exactly as `&mut` does
//@ accept-means: `f` returns 7, so `result@ == 0` is FALSE.
//@ fixed-by: wp-s59 loop-invalidated parameter facts in the ensures lane
//@ teeth: verified ✓ (exit 0) on wp-campaign 03a35447 — A/B'd with the driver crates checked out at that commit and rebuilt in place
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*b)@ == 0)]
#[ensures(result@ == 0)]
pub fn f(b: &mut Box<u32>) -> u32 {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { **b = 7; i += 1; }
    **b
}
