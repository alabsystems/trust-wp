//@ expect: reject
//@ mechanism: an obligation that PRECEDES a `#[trusted] proof_assert!` must be proved without it; assumed at entry, the later fact discharged the earlier overflow check
//@ accept-means: `x + 1` was proved not to overflow from a fact the program only trusts after the addition
//@ verdict: failed
//@ fn-failed: bump
//@ fixed-by: trusted_assertion_entry_refusal (the trusted fact is assumed at entry only where entry and program point agree)
//@ teeth: measured — before the fix `bump verified ✓` on the false contract (exit 2 only through `assumed=1`); after it `not assumed (a branch, call, assertion or drop precedes it)` and `bump FAILED ✗`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: bump(u32::MAX) overflows before the trusted fact is reached.
#[ensures(result@ == x@ + 1)]
pub fn bump(x: u32) -> u32 {
    let y = x + 1;
    #[trusted]
    proof_assert! { x < 10u32 };
    y
}
