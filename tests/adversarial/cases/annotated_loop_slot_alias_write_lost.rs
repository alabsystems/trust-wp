//@ expect: reject
//@ mechanism: moved_borrow_double_hop_write_lost with its write wrapped in an annotated loop.
//@ mechanism: The slot-alias record does havoc the root here, and the annotated-loop lane
//@ mechanism: re-grants the precise resolve afterwards, so the closed hop is open again.
//@ accept-means: every case in the moved_borrow_slot_* family can be re-opened by putting one
//@ accept-means: annotated loop around the write; the slot-alias havoc is not the last word on
//@ accept-means: the parameter's final value.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; f(&mut v); afterwards
//@ v == 9, so `^r` is 9 while `*r` is 0.
//@ teeth: OPEN. Measured ACCEPTED, exit 0, both with and without the slot-alias record, while
//@ teeth: the same body with the loop removed (moved_borrow_double_hop_write_lost) is rejected.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut q = r;
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        let s = &mut q;
        **s = 9;
        i += 1;
    }
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
