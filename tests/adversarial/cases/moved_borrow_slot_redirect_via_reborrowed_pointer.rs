//@ expect: reject
//@ mechanism: moved_borrow_slot_redirect_other_root_write_lost with the redirect performed
//@ mechanism: through a REBORROW of the slot pointer. `&mut *s` carries no slot-alias record of
//@ mechanism: its own — the lane that registers one fires only for a borrow OF a slot, not for
//@ mechanism: a borrow THROUGH a pointer to one — so a repair that widened the record on `s` to
//@ mechanism: every root the slot could hold would never see this redirect, while the write
//@ mechanism: through `**s` still reaches b's referent. The case exists to say which of the two
//@ mechanism: repairs is the one that closes the family.
//@ accept-means: the redirect is invisible whenever it is spelled through one more reference
//@ accept-means: layer, so `b` keeps its identity resolve while the write lands on its pointee.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut x = 0; let mut y = 0;
//@ f(&mut x, &mut y); afterwards y == 9, so `^b` is 9 while `*b` is 0.
//@ fixed-by: D-79 (a tracked borrow stored through a deref escapes the tracker)
//@ teeth: verified — ACCEPTED, exit 0, with the D-79 escape havoc disabled by a one-line early
//@ teeth: return, and rejected with it. The redirect through `&mut *s` is the spelling that says
//@ teeth: the charge belongs at the STORE and not on the slot pointer's own alias record.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^b == *b)]
pub fn f(a: &mut i32, b: &mut i32) {
    let mut p = a;
    let s = &mut p;
    {
        let t = &mut *s;
        *t = b;
    }
    **s = 9;
}

pub fn caller() {
    let mut x = 0i32;
    let mut y = 0i32;
    f(&mut x, &mut y);
    assert!(y == 9);
}
