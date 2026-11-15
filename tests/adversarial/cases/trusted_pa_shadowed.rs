//@ expect: reject
//@ mechanism: the trusted expression names a `let` that shadows an argument; read at function entry the name resolves to the argument instead
//@ accept-means: `y == 0`, true of the shadowing local, was assumed of the argument `y` and proved `shadowed` returns 0 for every input
//@ verdict: failed
//@ fn-failed: shadowed
//@ fixed-by: trusted_assertion_entry_refusal (the trusted fact is assumed at entry only where entry and program point agree)
//@ teeth: measured — before the fix `shadowed verified ✓` on the false contract (exit 2 only through `assumed=1`); after it `not assumed (`y` does not name exactly one argument)` and `shadowed FAILED ✗`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: shadowed(5) returns 5.
#[ensures(result == 0i32)]
pub fn shadowed(y: i32) -> i32 {
    let old = y;
    let y = 0i32;
    #[trusted]
    proof_assert! { y == 0i32 };
    old
}
