//@ expect: reject
//@ mechanism: the loop writes the parameter's pointee through a REBORROW (`let r = &mut *a; *r = 7`); the entry fact about `*a` still discharged the postcondition
//@ accept-means: `f` returns 7, so `result@ == 0` is FALSE.
//@ fixed-by: wp-s59 loop-invalidated parameter facts in the ensures lane
//@ teeth: NO TEETH GAINED — already refused on wp-campaign 03a35447 (verdict `failed`, A/B 2026-09-14). Kept as a regression guard for the reborrow write shape, which the loop write-site walk must keep following.
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
    while i < 3 { let r = &mut *a; *r = 7; i += 1; }
    *a
}
