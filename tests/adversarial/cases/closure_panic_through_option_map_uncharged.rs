//@ expect: reject
//@ mechanism: a contract-free closure that always panics, handed to `Option::map`. Nothing but the
//@ mechanism: closure's own verification can charge its abort: the combinator's builtin spec owes
//@ mechanism: nothing for it, and the host's WP reads the closure only as a result value.
//@ accept-means: `pick` is reported `verified` although `pick(Some(1))` panics inside the closure.
//@ fixed-by: D-118
//@ teeth: ACCEPTED (exit 0, `pick verified`) on the binary before D-118; the closure is now
//@ teeth: refuted on its abort and `pick`'s credit is withdrawn.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// FALSE: `pick(Some(1))` panics.
#[ensures(result@ == 1)]
pub fn pick(o: Option<u32>) -> u32 {
    let _ = o.map(|_x| -> u32 { panic!() });
    1
}
