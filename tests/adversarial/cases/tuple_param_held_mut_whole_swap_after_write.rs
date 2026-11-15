//@ expect: reject
//@ verdict: failed
//@ refused-with: a postcondition reads that `&mut` only through `*`, `^` or `@`
//@ mechanism: the swap written `result == (x.1, x.0)` over a body that writes through `x.0` before it
//@ mechanism: swaps. Creusot reads `x.0` at entry, so `result.1` (whose current value is 5) is not it;
//@ mechanism: the owner's lane proved it, and the caller read `*p.1` as the entry value.
//@ accept-means: a postcondition read of a held `&mut` other than through `*`, `^` or `@` was placed
//@ accept-means: at a state the body had already written.
//@ WHY THE CONTRACT IS FALSE: `result.1` is `x.0` after `*x.0 = 5`; `x.0` in the postcondition is its
//@ WHY THE CONTRACT IS FALSE: entry value, whose current value is 0, so the caller's `*p.1 == 0` is false.
//@ fixed-by: D-181 — the whole read is refused at discovery.
//@ teeth: ACCEPTED (exit 0) on a build of this branch whose discovery check counts a held `&mut` read
//@ teeth: whole as placed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == (x.1, x.0))]
pub fn f<'a>(x: (&'a mut u32, &'a mut u32)) -> (&'a mut u32, &'a mut u32) {
    *x.0 = 5u32;
    (x.1, x.0)
}

pub fn caller() {
    let mut a = 0u32;
    let mut b = 0u32;
    let p = f((&mut a, &mut b));
    proof_assert!(*p.1 == 0u32);
}
