//@ expect: reject
//@ mechanism: a CONTRACT-FREE fn that calls a contracted LOCAL callee with an argument its
//@ mechanism: `#[requires]` forbids. Creusot emits a `callee requires` goal at the call site.
//@ mechanism: trust-wp's call lane emits it too — but only inside a body that is itself a
//@ mechanism: verification target (D-25), which a contract-free caller was not, so the callee's
//@ mechanism: precondition was granted at the callee and owed by nobody.
//@ accept-means: a precondition was laundered by putting the call in a function with no contract
//@ fixed-by: the contract-free abort/callee-precondition discovery pass
//@ teeth: verified — ACCEPTED on this branch's parent commit, rejected after the pass lands
//@ also-verified: need, anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(y@ != 0u32@)]
#[ensures(result@ == y@)]
pub fn need(y: u32) -> u32 {
    y
}

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// `need`'s precondition is violated here.
pub fn hop() {
    let _ = need(0u32);
}
