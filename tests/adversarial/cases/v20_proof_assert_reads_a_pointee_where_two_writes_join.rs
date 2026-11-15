//@ expect: reject
//@ mechanism: a `proof_assert!` reads memory two writes reach on different paths: `*x = 0; if c {
//@ mechanism: *x = 5; }` (b4), the same with `else { *x = 0; }` (b4m), a copy taken after the join
//@ mechanism: (b4n), a float condition (b6), and a local borrow `r = &mut y` written the same way
//@ mechanism: (b4l, b4l2) or twice on one arm (b4k: `*r = 1; if c { *r = 2; *r = 3; }`). D-185
//@ mechanism: read `*x` through the walk's recorded value whenever every write reaching the
//@ mechanism: assertion was a whole-pointee store through `x`, and the body
//@ mechanism: extraction's path-guarded write facts (`c ==> *x == 0` from the first store on the
//@ mechanism: then path, `c ==> *x == 5` from the second) were rewritten to the value at the
//@ mechanism: assertion, `ite(c, 5, 0)`, where together they say `!c`: the false goal was proved.
//@ accept-means: an assertion is credited from facts that equate the memory two stores left at two
//@ accept-means: program points, or from one store's value where another may be the one it sees.
//@ WHY THE CONTRACT IS FALSE: with `c` true (`f = 1.0` for b6) every second write runs: `*x` (and
//@ WHY THE CONTRACT IS FALSE: `*r`, `v`) is 5 at the assertion, never 0 or 1; b4l's and b4k's `!c` is
//@ WHY THE CONTRACT IS FALSE: false; b4m asserts `*x == 0` where the then branch left 5.
//@ fixed-by: D-186 (a read takes a store's recorded value only when that store is the one
//@ fixed-by: definition reaching it on every path; an effect fact reading memory a write changed
//@ fixed-by: before the assertion is dropped)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on 4c67cea8 (D-185) every proof_assert here was VERIFIED and the crate ACCEPTED; with
//@ teeth: D-186 b4, b4m, b6 and b4l2 are refused as stale reads and b4n, b4l and b4k are FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn b4(x: &mut i32, c: bool) {
    *x = 0i32;
    if c {
        *x = 5i32;
    }
    proof_assert!(*x == 0i32);
}

pub fn b4m(x: &mut i32, c: bool) {
    *x = 0i32;
    if c {
        *x = 5i32;
    } else {
        *x = 0i32;
    }
    proof_assert!(*x == 0i32);
}

pub fn b4n(x: &mut i32, c: bool) {
    *x = 1i32;
    if c {
        *x = 5i32;
    }
    let v = *x;
    proof_assert!(v == 1i32);
}

pub fn b6(x: &mut i32, f: f64) {
    *x = 0i32;
    if f > 0.5 {
        *x = 5i32;
    }
    proof_assert!(*x == 0i32);
}

pub fn b4l(c: bool) {
    let mut y = 1i32;
    let r = &mut y;
    *r = 0i32;
    if c {
        *r = 5i32;
    }
    proof_assert!(!c);
}

pub fn b4l2(c: bool) {
    let mut y = 1i32;
    let r = &mut y;
    *r = 0i32;
    if c {
        *r = 5i32;
    }
    proof_assert!(*r == 0i32);
}

pub fn b4k(c: bool) {
    let mut y = 0i32;
    let r = &mut y;
    *r = 1i32;
    if c {
        *r = 2i32;
        *r = 3i32;
    }
    proof_assert!(!c);
}
