//@ expect: reject
//@ mechanism: The body of moved_borrow_slot_pointer_redirect_control, read against the OTHER
//@ mechanism: parameter. A pointer into a moved borrow's slot is recorded against the root the
//@ mechanism: slot held WHEN THE POINTER WAS TAKEN, not the borrow it holds at the write. The
//@ mechanism: assignment `*s = b` redirects the slot, so the write through `**s` reaches b's
//@ mechanism: referent while the alias record still names a. The havoc lands on a — which the
//@ mechanism: write cannot reach — and b keeps its identity resolve `b_final == b_current`.
//@ accept-means: the slot-alias record charges the write to a root chosen at the borrow site,
//@ accept-means: so any redirect between the borrow and the write havocs one parameter and
//@ accept-means: credits the other. One parameter is over-refused and the other is a free
//@ accept-means: prophecy; the sibling control records only the over-refusal.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut x = 0; let mut y = 0;
//@ f(&mut x, &mut y); afterwards y == 9 — the redirect put b's borrow in the slot — so `^b`
//@ is 9 while `*b` is 0.
//@ fixed-by: D-79 (a tracked borrow stored through a deref escapes the tracker)
//@ teeth: verified — ACCEPTED, exit 0, "trust-wp: f verified ✓", with the D-79 escape havoc
//@ teeth: disabled by a one-line early return, and rejected with it. It was ACCEPTED on the
//@ teeth: driver built without the slot-alias record too: the record changed which root is
//@ teeth: wrong, not whether one is. The no-pointer spelling (`let mut p = a; p = b; *p = 9;`)
//@ teeth: is rejected, so the pointer is load-bearing.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^b == *b)]
pub fn f(a: &mut i32, b: &mut i32) {
    let mut p = a;
    let s = &mut p;
    *s = b;
    **s = 9;
}

pub fn caller() {
    let mut x = 0i32;
    let mut y = 0i32;
    f(&mut x, &mut y);
    assert!(y == 9);
}
