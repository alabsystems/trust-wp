//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: The pointer into the moved borrow's slot is carried in a TUPLE and the write
//@ mechanism: goes through the tuple field. The struct spelling and the tuple spelling reach
//@ mechanism: the aggregate lanes by different routes, so each needs its own tooth.
//@ accept-means: a tuple launders the extra reference layer, leaving `^r == *r` granted for a
//@ accept-means: body that changes the pointee.
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
    let t = (&mut q, 0i32);
    **t.0 = 9;
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
