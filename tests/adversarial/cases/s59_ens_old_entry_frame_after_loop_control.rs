//@ expect: verify
//@ xfail: over-refused on wp-campaign 03a35447 already (verdict unknown, A/B 2026-09-14) — `old((*a)@)` past a loop that writes `*a` is a campaign-owned gap, not wp-s59's. Kept so the frame distinction is pinned: `old` is the ENTRY frame and a loop cannot disturb it.
//@ mechanism: control: `old((*a)@)` is the ENTRY frame and a loop cannot disturb it; the copy taken before the loop is genuinely that value
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == old((*a)@))]
pub fn f(a: &mut u32) -> u32 {
    let r = *a;
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { *a = 7; i += 1; }
    r
}
