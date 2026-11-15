//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: The `&mut &mut` hop of moved_borrow_double_hop_write_lost with the pointer
//@ mechanism: MOVED to a second local before the write. The alias record has to travel with
//@ mechanism: the pointer across a plain `Use`; a registration that only ever fires at the
//@ mechanism: borrow site leaves this spelling accepted.
//@ accept-means: the alias that a write through the extra reference layer must be charged
//@ accept-means: against is forgotten by a move, so `let t = s; **t = v` is a hole beside a
//@ accept-means: closed `**s = v`.
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
    let s = &mut q;
    let t = s;
    **t = 9;
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
