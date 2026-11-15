//@ expect: reject
//@ mechanism: `lend` returns its `&mut` parameter, so the final value of `x` is its caller's to
//@ mechanism: decide, through the returned borrow. Its own lane refuted `resolve(x)`, but a call read
//@ mechanism: the clause over the argument's borrow as `*b == ^b` (D-109's reading of an annotated
//@ mechanism: borrow, over a final value the caller's lane minted for it), and the caller inherited
//@ mechanism: the false claim that the borrow it lent is resolved at the call: `a`'s final value was
//@ mechanism: pinned to its value there, and `opaque(r)` (contract `true`) cannot contradict it.
//@ accept-means: `exploit` is credited with `result == 3` although it returns 5, over a callee
//@ accept-means: contract no lane proves.
//@ WHY THE CONTRACT IS FALSE: `lend` hands `x` to its caller in the returned borrow, and the caller
//@ WHY THE CONTRACT IS FALSE: writes 5 through it (`opaque`), so `x` is not resolved at the return,
//@ WHY THE CONTRACT IS FALSE: and `exploit` returns `a == 5`.
//@ fixed-by: D-126 (`resolve` of a borrow whose final value the lane does not name is refused, in
//@ fixed-by: the callee's lane and at the call)
//@ teeth: MEASURED (debug driver, ay 57a37e51): on 2a548aca `lend` FAILED and `exploit` verified
//@ teeth: (TEETH LOST); on D-126 both are refused (`resolve refused (fail-closed)`) and opaque
//@ teeth: verifies.
//@ also-verified: opaque
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{prelude::*, resolve::Resolve};

#[ensures(resolve(x))]
pub fn lend(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(true)]
pub fn opaque(x: &mut i32) {
    *x = 5;
}

#[ensures(result == 3i32)]
pub fn exploit() -> i32 {
    let mut a = 3i32;
    let r = lend(&mut a);
    opaque(r);
    a
}
