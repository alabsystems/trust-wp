//@ expect: reject
//@ mechanism: `stash` stores the borrow of a `Range<i32>` in another parameter's slot, and whoever
//@ mechanism: holds the slot writes or advances the range after the call, so `^it == *it` has no
//@ mechanism: reading in `stash`'s lane or at a call (D-107's lend rule). The `next` through the
//@ mechanism: slot is a foreign call, read at the type it returns (`Option<i32>`), so its `^self`
//@ mechanism: is granted: the lend must still be refused beside it.
//@ accept-means: reading a foreign call at its instance let the final value of a borrow lent into
//@ accept-means: another holder through, or the lend rule no longer refuses a range.
//@ WHY THE CONTRACT IS FALSE: each caller leaves `(^it).start` at 1, written through the slot or
//@ WHY THE CONTRACT IS FALSE: advanced by `next` from the 0 the precondition fixes.
//@ fixed-by: D-107 (lend into another parameter); kept beside D-124's instance reading
//@ teeth: MEASURED (debug driver) on 576532d7, before the lend rule: `stash_then_write verified`
//@ teeth: and `stash_then_advance verified` (the call read as written, `next` granted). With the
//@ teeth: foreign calls read at their instance, `stash`'s clause is refused by name and both
//@ teeth: callers carry its fail-closed `false` (`stash_then_advance` may report the timeout of
//@ teeth: the solve over that goal set).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::ops::Range;

use creusot_std::prelude::*;

#[ensures(^it == *it)]
pub fn stash<'a>(it: &'a mut Range<i32>, slot: &mut Option<&'a mut Range<i32>>) {
    *slot = Some(it);
}

#[requires((*it).start == 0i32 && (*it).end == 10i32)]
#[ensures((^it).start == 0i32)]
pub fn stash_then_write(it: &mut Range<i32>) {
    let mut slot: Option<&mut Range<i32>> = None;
    stash(it, &mut slot);
    if let Some(s) = slot {
        s.start = 1i32;
    }
}

#[requires((*it).start == 0i32 && (*it).end == 10i32)]
#[ensures((^it).start == 0i32)]
pub fn stash_then_advance(it: &mut Range<i32>) {
    let mut slot: Option<&mut Range<i32>> = None;
    stash(it, &mut slot);
    if let Some(s) = slot {
        let _ = s.next();
    }
}
