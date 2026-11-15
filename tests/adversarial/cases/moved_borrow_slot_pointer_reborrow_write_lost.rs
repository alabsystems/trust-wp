//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: The `&mut &mut` hop of moved_borrow_double_hop_write_lost with the write going
//@ mechanism: through a REBORROW of the pointer (`&mut *s`) rather than the pointer itself.
//@ accept-means: the extra-layer alias is lost again one reborrow later, so closing the
//@ accept-means: direct spelling alone would leave the family live.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; f(&mut v); afterwards
//@ v == 9, so `^r` is 9 and `*r` is 0.
//@ teeth: MEASURED as ACCEPTED, exit 0, on the driver built without the slot-alias record,
//@ teeth: and rejected with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut q = r;
    let mut s = &mut q;
    let t = &mut *s;
    **t = 9;
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
