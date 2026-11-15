//@ expect: verify
//@ mechanism: the in-domain twin of the out-of-domain postcondition grant — the same two `ensures` clauses instantiated at an argument the `#[requires]` admits, where both are genuine consequences of the definition.
//@ accept-means: n/a (control) — `idl(2) == 2 && idl(2) >= 0` is TRUE; a rejection here would mean a fix for the out-of-domain grant had also thrown away the legitimate use of a logic function's postcondition inside its own domain.
//@ fixed-by: ?
//@ teeth: verifies today (exit 0), so it separates "the grant is refused outside the domain" from "the grant was deleted"; it is the half of the pair that must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic(open)]
#[requires(x >= 0)]
#[ensures(result == x)]
#[ensures(result >= 0)]
pub fn idl(x: Int) -> Int {
    x
}

#[ensures(result@ == 1)]
pub fn c() -> u32 {
    proof_assert!(idl(2) == 2 && idl(2) >= 0);
    1u32
}
