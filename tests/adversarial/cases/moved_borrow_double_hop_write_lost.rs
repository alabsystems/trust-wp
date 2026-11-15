//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: A `&mut` parameter is MOVED into a local, the local is reborrowed (`&mut q`,
//@ mechanism: a `&mut &mut i32`), and the write goes through the double dereference `**s`.
//@ mechanism: The deref-write owner resolver reads only the innermost deref's base — the
//@ mechanism: intermediate `&mut &mut` local — and finds no reaching definition that names
//@ mechanism: the moved parameter, so the write is attributed to nothing. The parameter is
//@ mechanism: then seen as untouched and the identity resolve `r_final == r_current` is
//@ mechanism: emitted, which is exactly the false premise `^r == *r`.
//@ accept-means: a `&mut` whose write passes through one extra reference layer keeps a
//@ accept-means: prophecy that is GRANTED as the entry value while the body changes the
//@ accept-means: pointee. Every `^`-bearing postcondition over such a borrow is worthless,
//@ accept-means: and the grant reaches ordinary callers unchanged.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; f(&mut v); afterwards
//@ v == 9, so the borrow's final value is 9 while `*r` — its entry value — is 0.
//@ teeth: MEASURED as ACCEPTED, exit 0, `trust-wp: f verified ✓`, "1 verified, 0 failed".
//@ teeth: The write is genuinely invisible rather than merely unproven: the TRUE claim
//@ teeth: `#[ensures(^r == 9)]` on this identical body is NOT provable (unknown).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut q = r;
    let s = &mut q;
    **s = 9;
}

// The refutation, in executable Rust: `v` enters at 0 and leaves at 9.
pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
