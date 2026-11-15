//@ expect: reject
//@ mechanism: the `if let` spelling of an arm premise (D-169): `below(x)` runs on the `Some` arm of an
//@ mechanism: `Option` discriminant switch. Its postcondition holds only where that arm ran; unscoped,
//@ mechanism: `ensures(result@ < 100)` follows on the `None` path, which returns `x` unchanged.
//@ accept-means: a contract is verified from a callee postcondition on an execution that never calls it,
//@ accept-means: and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, None)` returns 200.
//@ teeth: ACCEPTED at the campaign tip; rejected with D-169.
//@ verdict: failed
//@ fn-failed: f
//@ also-verified: below
//@ fixed-by: D-169 (each premise an arm walk records is scoped to that arm's edge).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100 && result == x)]
pub fn below(x: u32) -> u32 {
    #[invariant(true)]
    while x >= 100 {}
    x
}

#[ensures(result@ < 100)]
pub fn f(x: u32, o: Option<u8>) -> u32 {
    if let Some(_) = o { below(x); }
    x
}
