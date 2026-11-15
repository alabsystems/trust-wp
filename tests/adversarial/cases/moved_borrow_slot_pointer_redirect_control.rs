//@ expect: verify
//@ xfail: over-refusal, and the named price of the slot-alias record. The write through the
//@ xfail: pointer havocs the root the pointer was registered against, but the assignment
//@ xfail: `*s = b` had already redirected the slot, so the write lands on `b` and `a` is the
//@ xfail: one root it cannot reach. Retire this when the alias record tracks WHICH borrow the
//@ xfail: slot currently holds instead of naming the root it held when the pointer was taken.
//@ mechanism: `a` is moved into a local, a pointer to that local's slot replaces the borrow it
//@ mechanism: holds with `b`'s, and the write through the pointer therefore reaches `b`. `a`'s
//@ mechanism: borrow died at the reassignment with its pointee untouched, so `^a == *a` is
//@ mechanism: TRUE — this case exists so the refusal is recorded as a cost rather than found
//@ mechanism: later as a mystery.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^a == *a)]
pub fn f(a: &mut i32, b: &mut i32) {
    let mut p = a;
    let s = &mut p;
    *s = b;
    **s = 9;
}
