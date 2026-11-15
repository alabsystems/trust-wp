//@ expect: reject
//@ mechanism: `stash` stores the borrow of `p` in `*slot`, another parameter's referent, so the
//@ mechanism: value `p` is left with is whatever the holder of `slot` leaves it, after the call.
//@ mechanism: D-102 decided lending from the return type alone: each call read the callee's
//@ mechanism: `^p == *p` (and the pre-Creusot `*p == old(*p)`, rewritten to the same) as a fact
//@ mechanism: and credited the caller with its argument unchanged, though no lane proved it.
//@ accept-means: a caller is credited with the final value of a borrow it lent into another
//@ accept-means: argument and wrote through afterwards.
//@ WHY THE CONTRACT IS FALSE: each caller writes 5 through the slot, so `^x` is 5 and the
//@ WHY THE CONTRACT IS FALSE: precondition makes the entry `*x` something else.
//@ fixed-by: D-107 (a `&mut` parameter whose region another parameter's writable memory may
//@ fixed-by: name is lent into it; a read of its final value, in either dialect, has no reading)
//@ teeth: MEASURED (debug driver) on 576532d7: `stash` and `stash_old` unknown, `stash_caller`
//@ teeth: and `stash_old_caller` verified. On the D-107 tree both callee clauses are refused
//@ teeth: by name and both callers are unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^p == *p)]
pub fn stash<'a>(p: &'a mut i32, slot: &mut Option<&'a mut i32>) {
    *slot = Some(p);
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    stash(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

#[ensures(*p == old(*p))]
pub fn stash_old<'a>(p: &'a mut i32, slot: &mut Option<&'a mut i32>) {
    *slot = Some(p);
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_old_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    stash_old(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}
