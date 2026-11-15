//@ expect: reject
//@ verdict: failed
//@ refused-with: a postcondition reads that `&mut` only through `*`, `^` or `@`
//@ mechanism: a whole read of a held `&mut` (`result.0 == x.0`) beside `old(..)` of its parameter,
//@ mechanism: after the body wrote through it. The owner's lane proved the clause.
//@ accept-means: a postcondition read of a held `&mut` other than through `*`, `^` or `@` was proved
//@ accept-means: over a body that wrote through it.
//@ WHY THE CONTRACT IS FALSE: in Creusot's reading `x.0` is the entry borrow, whose current value is 0,
//@ WHY THE CONTRACT IS FALSE: while `result.0` holds 5; the caller's `*r.0 == 0` is false after the call.
//@ fixed-by: D-181 — the whole read is refused at discovery.
//@ teeth: on a build of this branch whose discovery check counts a held `&mut` read whole as placed,
//@ teeth: `f verified` on this false clause (the per-function gate reports it); the caller's
//@ teeth: assertion was unknown there.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result.0 == x.0 && result.1 == old(x.1))]
pub fn f<'a>(x: (&'a mut u32, u32)) -> (&'a mut u32, u32) {
    *x.0 = 5u32;
    x
}

pub fn caller() {
    let mut a = 0u32;
    let r = f((&mut a, 0u32));
    proof_assert!(*r.0 == 0u32);
}
