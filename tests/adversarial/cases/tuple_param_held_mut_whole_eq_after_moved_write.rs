//@ expect: reject
//@ verdict: failed
//@ refused-with: a postcondition reads that `&mut` only through `*`, `^` or `@`
//@ mechanism: the held `&mut` is moved out of the parameter, written through, and returned in a new
//@ mechanism: tuple; `result.0 == x.0` compares it whole. The owner's lane proved the entry borrow equal
//@ mechanism: to the written one, and the caller read `*r.0` as the entry value.
//@ accept-means: a postcondition read of a held `&mut` other than through `*`, `^` or `@` was placed
//@ accept-means: at entry although the body wrote through the `&mut` after moving it out.
//@ WHY THE CONTRACT IS FALSE: `*r.0` is 5 after the call; `x.0` in the postcondition is the entry borrow,
//@ WHY THE CONTRACT IS FALSE: whose current value is 0.
//@ fixed-by: D-181 — the whole read is refused at discovery.
//@ teeth: ACCEPTED (exit 0) on a build of this branch whose discovery check counts a held `&mut` read
//@ teeth: whole as placed. The same clause over `*x.0 = 5; x` is unknown there, not proved: the move
//@ teeth: out of the parameter is what the lane loses.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result.0 == x.0)]
pub fn f<'a>(x: (&'a mut u32, u32)) -> (&'a mut u32, u32) {
    let (p, n) = x;
    *p = 5u32;
    (p, n)
}

pub fn caller() {
    let mut a = 0u32;
    let r = f((&mut a, 0u32));
    proof_assert!(*r.0 == 0u32);
}
