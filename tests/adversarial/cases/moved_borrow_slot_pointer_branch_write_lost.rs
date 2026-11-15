//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: The write through the slot pointer happens on ONE branch only. A resolve that
//@ mechanism: is emitted unconditionally states `^r == *r` on the path that writes too, so a
//@ mechanism: conditional write is the same hole with a merge in front of it.
//@ accept-means: the identity resolve is granted for a function that changes the pointee on
//@ accept-means: some of its paths, which is every `if` away from the unconditional spelling.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; f(&mut v, true);
//@ afterwards v == 9, so `^r` is 9 and `*r` is 0.
//@ teeth: MEASURED as ACCEPTED, exit 0, on the driver built without the slot-alias record,
//@ teeth: and rejected with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32, c: bool) {
    let mut q = r;
    let s = &mut q;
    if c {
        **s = 9;
    }
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v, true);
    assert!(v == 9);
}
