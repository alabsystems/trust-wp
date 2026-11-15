//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: The `&mut &mut` hop of moved_borrow_double_hop_write_lost over a struct
//@ mechanism: pointee: the write is a FIELD store `(**s).a = 9` rather than a whole-pointee
//@ mechanism: store. The field-write lane and the whole-pointee lane resolve the owner
//@ mechanism: separately, so a fix in one of them leaves the other accepted.
//@ accept-means: the identity resolve survives a field store through the extra reference
//@ accept-means: layer, so `^r == *r` is granted for a struct the body mutates.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut s = S { a: 0 }; f(&mut s);
//@ afterwards s.a == 9, so `^r` and `*r` differ in their `a` field.
//@ teeth: MEASURED as ACCEPTED, exit 0, "1 verified, 0 failed".
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub a: i32,
}

#[ensures(^r == *r)]
pub fn f(r: &mut S) {
    let mut q = r;
    let s = &mut q;
    (**s).a = 9;
}

pub fn caller() {
    let mut s = S { a: 0 };
    f(&mut s);
    assert!(s.a == 9);
}
