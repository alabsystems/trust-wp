//@ expect: reject
//@ verdict: failed
//@ refused-with: a postcondition reads that `&mut` only through `*`, `^` or `@`
//@ mechanism: the grant side of a whole read of a held `&mut`: `result.0 == x.0` over a body that
//@ mechanism: writes through `x.0`. A caller granted the clause reads `*r.0` as the entry value.
//@ accept-means: a caller was granted a postcondition that reads a held `&mut` whole, which no lane
//@ accept-means: places.
//@ WHY THE CONTRACT IS FALSE: `*r.0` is 5 after the call, and `x.0` in the postcondition is the entry
//@ WHY THE CONTRACT IS FALSE: borrow, whose current value is 0.
//@ fixed-by: D-181 — the clause is refused at discovery, so no caller is granted it.
//@ teeth: on a build of this branch whose discovery check counts a held `&mut` read whole as placed,
//@ teeth: `f` is unknown and the caller's false `*r.0 == 0u32` verified (the per-assertion gate
//@ teeth: reports it).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result.0 == x.0)]
pub fn f<'a>(x: (&'a mut u32, u32)) -> (&'a mut u32, u32) {
    *x.0 = 5u32;
    x
}

pub fn caller() {
    let mut a = 0u32;
    let r = f((&mut a, 0u32));
    proof_assert!(*r.0 == 0u32);
}
