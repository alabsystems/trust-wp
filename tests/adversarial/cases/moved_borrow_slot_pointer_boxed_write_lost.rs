//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: The pointer into the moved borrow's slot is BOXED and the write goes through
//@ mechanism: the box (`***b = 9`), which puts a heap indirection between the write and the
//@ mechanism: alias record as well as the extra reference layer.
//@ accept-means: a Box around the slot pointer is enough to make the write invisible and the
//@ accept-means: identity resolve survive.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; f(&mut v); afterwards
//@ v == 9, so `^r` is 9 and `*r` is 0.
//@ teeth: MEASURED as ACCEPTED, exit 0, on the driver built without the slot-alias record,
//@ teeth: and refuted with a counterexample with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut q = r;
    let b = Box::new(&mut q);
    ***b = 9;
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
