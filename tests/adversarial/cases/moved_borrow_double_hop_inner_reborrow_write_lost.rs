//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: The `&mut &mut` hop of moved_borrow_double_hop_write_lost, with the write
//@ mechanism: taken one step further away: a reborrow `&mut **s` is bound to a fresh local
//@ mechanism: and written through that. The owner resolver still stops at the intermediate
//@ mechanism: double reference, so neither the reborrow nor the moved parameter is credited
//@ mechanism: with the write and the identity resolve is emitted for the parameter.
//@ accept-means: the refusal that covers a direct `*q = v` after a move does not survive a
//@ accept-means: reborrow out of a double reference, so a blanket "moved borrow" guard is
//@ accept-means: not what is protecting this shape.
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
    let s = &mut q;
    let t = &mut **s;
    *t = 9;
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
