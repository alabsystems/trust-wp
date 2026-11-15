//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: Two `&mut` parameters are moved into locals and the LOCALS' slots are swapped,
//@ mechanism: so the write through `q` lands on `a`'s referent. The nested-transfer lane
//@ mechanism: recognizes `swap` between two PARAMETER slots; between two moved-borrow locals
//@ mechanism: the slot pointers named no tracked root, the swap moved the borrow with nothing
//@ mechanism: recording it, and `a` was left reading as untouched.
//@ accept-means: a swap of two borrow-holding locals redirects a write to a place the
//@ accept-means: prophecy lane still reports at its entry value, in both directions at once.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut x = 0; let mut y = 0;
//@ f(&mut x, &mut y); afterwards x == 9 — the swap put `a`'s borrow in `q` — so `^a` is 9
//@ while `*a` is 0.
//@ teeth: MEASURED as ACCEPTED, exit 0, on the driver built without the slot-alias record,
//@ teeth: and rejected with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^a == *a)]
pub fn f(a: &mut i32, b: &mut i32) {
    let mut p = a;
    let mut q = b;
    core::mem::swap(&mut p, &mut q);
    *q = 9;
}

pub fn caller() {
    let mut x = 0i32;
    let mut y = 0i32;
    f(&mut x, &mut y);
    assert!(x == 9);
}
