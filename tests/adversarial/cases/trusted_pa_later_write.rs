//@ expect: reject
//@ mechanism: a `#[trusted] proof_assert!` is assumed as an ENTRY fact of its function's contract proof (effective_requires), while Creusot assumes it where it is written (`-{e}-`); a write before the assertion makes the entry reading a different, false fact
//@ accept-means: the trusted fact, TRUE where it is written (`y` was just set to 0), was read as `y == 0` about the ARGUMENT and proved that `launder` returns 0 for every input
//@ verdict: failed
//@ fn-failed: launder
//@ fixed-by: trusted_assertion_entry_refusal (the trusted fact is assumed at entry only where entry and program point agree)
//@ teeth: measured — before the fix `launder verified ✓` on the false contract (exit 2 only through `assumed=1`); after it `not assumed (a write to an argument precedes it)` and `launder FAILED ✗`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: launder(5) returns 5.
#[ensures(result == 0i32)]
pub fn launder(mut y: i32) -> i32 {
    let old = y;
    y = 0i32;
    #[trusted]
    proof_assert! { y == 0i32 };
    old
}
