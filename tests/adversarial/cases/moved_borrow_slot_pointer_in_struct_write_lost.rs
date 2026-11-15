//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: The pointer into the moved borrow's slot is carried in a struct field and the
//@ mechanism: write goes through that field (`**h.p = 9`). The aggregate-escape lane havocs
//@ mechanism: a tracked BORROW moved into an aggregate; a pointer to the borrow's SLOT is a
//@ mechanism: different value with the same reach, and it was not a tracked root at all.
//@ accept-means: a struct is enough to launder the extra reference layer, so the alias
//@ accept-means: record must be what makes the pointer a tracked root, not the write site.
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

pub struct H<'a, 'b> {
    pub p: &'a mut &'b mut i32,
}

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut q = r;
    let h = H { p: &mut q };
    **h.p = 9;
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
