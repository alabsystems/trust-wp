//@ expect: reject
//@ mechanism: moved_borrow_slot_redirect_other_root_write_lost seen from an ordinary caller
//@ mechanism: that names no prophecy at all. The free final value reaches it through the
//@ mechanism: callee's postcondition, so the hole is not confined to `^`-bearing contracts.
//@ accept-means: a caller reads its own local back at the entry value after a callee wrote
//@ accept-means: through it, and the false premise is invisible in the caller's own text.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: go() returns 9, not 0.
//@ fixed-by: D-79 (a tracked borrow stored through a deref escapes the tracker)
//@ teeth: verified — ACCEPTED, exit 0, with the D-79 escape havoc disabled by a one-line early
//@ teeth: return, and rejected with it. It was ACCEPTED with and without the slot-alias record.
//@ also-verified: go
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

#[ensures(result == 0i32)]
pub fn go() -> i32 {
    let mut x = 0i32;
    let mut y = 0i32;
    f(&mut x, &mut y);
    y
}
