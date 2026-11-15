//@ expect: reject
//@ mechanism: the rusthorn `inc_max_3` body with both surviving slots incremented by 2. The
//@ mechanism: nested-slot expiry resolutions (`Final(<entry borrow>) == <slot exit value>`) are the
//@ mechanism: only premises that decide the three prophecies once the collapsed transfer credits
//@ mechanism: and the stale call-final ones are gone; they must decide them to the values the
//@ mechanism: program leaves, under which two of the three can be equal.
//@ accept-means: an expiry resolution names a value other than its slot's exit value, or a
//@ accept-means: collapsed transfer credit survived beside the resolutions.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let (mut a, mut b, mut c) = (0, 0, 0);
//@ inc_max_3(&mut a, &mut b, &mut c) leaves a == 2 and b == 2, so ^ma == ^mb.
//@ teeth: UNVERIFIED — rejected with the resolutions dropped by the stale call-final filter and
//@ teeth: with them applied after it; it pins the resolutions' values, not their presence.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
#[ensures(^mma == *mmb && ^mmb == *mma)]
fn swap<'a, 'b>(mma: &'a mut &'b mut u32, mmb: &'a mut &'b mut u32) {
    std::mem::swap(mma, mmb);
}

#[requires(*ma <= 1_000_000u32 && *mb <= 1_000_000u32 && *mc <= 1_000_000u32)]
#[ensures(^ma != ^mb && ^mb != ^mc && ^mc != ^ma)]
pub fn inc_max_3<'a>(mut ma: &'a mut u32, mut mb: &'a mut u32, mut mc: &'a mut u32) {
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    if *mb < *mc {
        swap(&mut mb, &mut mc);
    }
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    *ma += 2;
    *mb += 2;
}
