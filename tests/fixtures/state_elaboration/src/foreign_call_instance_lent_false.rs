// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A borrow lent into another holder beside a foreign call read at its
//! instance: `stash` stores the borrow of a `Range<i32>` in another
//! parameter's slot, whose holder writes or advances the range after the
//! call, so `^it == *it` has no reading in `stash`'s lane or at a call
//! (D-107). The `next` through the slot grants its `^self` (D-124); the lend
//! is refused beside it.

#![allow(unused)]

use std::ops::Range;

use trust_wp::prelude::*;

#[ensures(^it == *it)]
pub fn stash<'a>(it: &'a mut Range<i32>, slot: &mut Option<&'a mut Range<i32>>) {
    *slot = Some(it);
}

// FALSE: the slot's holder writes 1 into the start.
#[requires((*it).start == 0i32 && (*it).end == 10i32)]
#[ensures((^it).start == 0i32)]
pub fn stash_then_write(it: &mut Range<i32>) {
    let mut slot: Option<&mut Range<i32>> = None;
    stash(it, &mut slot);
    if let Some(s) = slot {
        s.start = 1i32;
    }
}

// FALSE: the slot's holder advances the range from 0 to 1.
#[requires((*it).start == 0i32 && (*it).end == 10i32)]
#[ensures((^it).start == 0i32)]
pub fn stash_then_advance(it: &mut Range<i32>) {
    let mut slot: Option<&mut Range<i32>> = None;
    stash(it, &mut slot);
    if let Some(s) = slot {
        let _ = s.next();
    }
}

fn main() {}
