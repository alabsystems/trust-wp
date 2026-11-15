//@ expect: reject
//@ mechanism: the `#[requires]` fact about the ENTRY view of a `&mut Vec` pointee survived a loop that pushes to it; the ensures lane discharged a false postcondition from it
//@ accept-means: `f` returns 3, so `result@ == 0` is FALSE; only the stale entry fact `v@.len() == 0` discharges it.
//@ fixed-by: wp-s59 loop-invalidated parameter facts in the ensures lane
//@ teeth: NO TEETH GAINED — already refused on wp-campaign 03a35447 (verdict `unknown`, A/B 2026-09-14). Kept as a regression guard for the `&mut Vec` twin: the entry fact is spelled on the PARAMETER (`v@.len()`), not on a deref.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(v@.len() == 0)]
#[ensures(result@ == 0)]
pub fn f(v: &mut Vec<u32>) -> usize {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { v.push(7); i += 1; }
    v.len()
}
