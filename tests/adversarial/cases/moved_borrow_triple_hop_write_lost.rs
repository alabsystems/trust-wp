//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: The `&mut &mut` hop of moved_borrow_double_hop_write_lost at one more level:
//@ mechanism: `&mut &mut &mut i32`, written through `***t`. A fix that special-cases a
//@ mechanism: single extra layer leaves this one accepted, which is why it ships separately.
//@ accept-means: the missing attribution is per-LAYER, not a one-off: any number of
//@ accept-means: intervening reference layers detaches the write from the prophecy it owes.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; f(&mut v); afterwards
//@ v == 9, so `^r` is 9 and `*r` is 0.
//@ teeth: MEASURED as ACCEPTED, exit 0, "1 verified, 0 failed".
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut q = r;
    let mut s = &mut q;
    let t = &mut s;
    ***t = 9;
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
