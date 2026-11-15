//@ expect: reject
//@ mechanism: the loop writes a FIELD of the struct behind the `&mut` parameter; the entry fact about that field survived
//@ accept-means: `f` returns 7, so `result@ == 0` is FALSE.
//@ fixed-by: wp-s59 loop-invalidated parameter facts in the ensures lane
//@ teeth: verified ✓ (exit 0) on wp-campaign 03a35447 — A/B'd with the driver crates checked out at 03a35447 and rebuilt in place
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S { pub x: u32 }

#[requires((*s).x@ == 0)]
#[ensures(result@ == 0)]
pub fn f(s: &mut S) -> u32 {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { s.x = 7; i += 1; }
    s.x
}
