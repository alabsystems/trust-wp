//@ expect: reject
//@ mechanism: after a transfer `swap` the slot `ma` holds `mb`'s entry borrow, so `*ma += 1`
//@ mechanism: writes what `mb` pointed at and `ma`'s own entry borrow expires unwritten. The
//@ mechanism: expiry resolution must credit the write to the borrow that sits in the slot at exit,
//@ mechanism: branch by branch, never to the slot's entry borrow.
//@ accept-means: a nested-slot resolution pins the entry borrow's prophecy to the slot's exit value.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let (mut a, mut b) = (0, 1);
//@ f(&mut a, &mut b) swaps (0 < 1) and increments b, so a is left 0 and ^ma == *ma, not *ma + 1.
//@ teeth: UNVERIFIED — rejected with the resolutions dropped by the stale call-final filter and
//@ teeth: with them applied after it; it pins which borrow a resolution names.
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

#[requires(*ma <= 1_000_000u32 && *mb <= 1_000_000u32)]
#[ensures(^ma == *ma + 1u32)]
pub fn f<'a>(mut ma: &'a mut u32, mut mb: &'a mut u32) {
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    *ma += 1;
}
