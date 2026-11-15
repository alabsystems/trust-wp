//@ expect: reject
//@ verdict: failed
//@ refused-with: a postcondition reads that `&mut` only through `*`, `^` or `@`
//@ mechanism: a postcondition compares the `&mut`s a tuple parameter holds whole (`result == (x.1,
//@ mechanism: x.0)`). The owner's lane reads a held `&mut` compared whole as its current value, so
//@ mechanism: under `*x.0 == *x.1` a body that does not swap proves the swap; every call reads the
//@ mechanism: same equality as which borrow the result holds, so the caller's write through `p.0`
//@ mechanism: is read as a write to `b`.
//@ accept-means: a postcondition read of a held `&mut` other than through `*`, `^` or `@` was placed,
//@ accept-means: and the owner proved it over a meaning its callers do not read.
//@ WHY THE CONTRACT IS FALSE: `f` returns `(x.0, x.1)`, so `result.0` is the borrow of `a`, not of
//@ WHY THE CONTRACT IS FALSE: `b`; after `*p.0 = 10`, `b` is still 0.
//@ fixed-by: D-181 — a postcondition that reads a held `&mut` whole (compared, bound or handed to a
//@ fixed-by: function) is refused at discovery; the caller is granted nothing and its assertion FAILS.
//@ teeth: ACCEPTED (exit 0) on a build of this branch whose discovery check counts a held `&mut` read
//@ teeth: whole as placed, which is how every lane read it before D-181.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*x.0 == *x.1)]
#[ensures(result == (x.1, x.0))]
pub fn f<'a>(x: (&'a mut u32, &'a mut u32)) -> (&'a mut u32, &'a mut u32) {
    (x.0, x.1)
}

pub fn caller() {
    let mut a = 0u32;
    let mut b = 0u32;
    let p = f((&mut a, &mut b));
    *p.0 = 10u32;
    proof_assert!(b == 10u32);
}
