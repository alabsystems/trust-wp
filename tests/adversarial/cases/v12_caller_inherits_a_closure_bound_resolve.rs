//@ expect: reject
//@ mechanism: A closure-style postcondition `|r: &mut i32| resolve(r) && ..` reads the returned
//@ mechanism: borrow as an unannotated `result`, and `encode_resolve` read an unannotated variable
//@ mechanism: the lane named no current or final state of as a by-value parameter, `true`, so the
//@ mechanism: callee's false claim that its returned borrow is resolved verified. D-109 made a caller
//@ mechanism: read `resolve(r)` of the call's (annotated) result borrow as `*r == ^r`, so the caller
//@ mechanism: inherited that false claim: `^x == ^r` and `*r == *x` pin `a`'s final value to its
//@ mechanism: value at the call, and `opaque(r)` (contract `true`) cannot contradict it.
//@ accept-means: `give2` verified with a claim about the borrow its caller holds, and `exploit5`
//@ accept-means: verified with `result == 3` though it returns 5.
//@ WHY THE CONTRACT IS FALSE: `give2` returns its argument; whoever holds the returned borrow
//@ WHY THE CONTRACT IS FALSE: decides its final value after the call (`opaque` writes 5 through it),
//@ WHY THE CONTRACT IS FALSE: so `resolve(r)` (`*r == ^r`) is no fact of `give2`, and `exploit5`
//@ WHY THE CONTRACT IS FALSE: returns `a == 5`.
//@ fixed-by: D-126 (an unannotated variable is not read as a value; `resolve` of a borrow whose
//@ fixed-by: final value the lane does not name is refused, in the callee's lane and at the call)
//@ teeth: The r11 review measured (ay 0e44aed6a) give2 verified and exploit5 FAILED on
//@ teeth: 9da9f9a8, and give2, opaque and exploit5 verified on 6a828d52 (D-109).
//@ teeth: MEASURED (debug driver, ay 57a37e51): bdbba131 verifies give2, opaque and exploit5
//@ teeth: (ACCEPTED); on D-126 give2 and exploit5 are refused (`resolve refused
//@ teeth: (fail-closed)`) and opaque verifies.
//@ note: a caller of a callee whose clause names the returned borrow's final value before its
//@ note: `resolve` (`^x == ^r && *r == *x && resolve(r)`) reads the clause over the final value the
//@ note: `^r` named, and is credited modularly over the callee's refused contract, as D-107 credits
//@ note: the callers of a raw-pointer lend; that credit is not this case's claim.
//@ also-verified: opaque
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{prelude::*, resolve::Resolve};

#[ensures(|r: &mut i32| resolve(r) && ^x == ^r && *r == *x)]
pub fn give2(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(true)]
pub fn opaque(x: &mut i32) {
    *x = 5;
}

#[ensures(result == 3i32)]
pub fn exploit5() -> i32 {
    let mut a = 3i32;
    let r = give2(&mut a);
    opaque(r);
    a
}
