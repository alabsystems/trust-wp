//@ expect: reject
//@ mechanism: a `#[trusted] proof_assert!` on one branch was assumed at function entry, so its premise also discharged the OTHER branch; Creusot assumes it only on the path that reaches it
//@ accept-means: the `else` branch, which trusts nothing, was proved from the `then` branch's trusted fact
//@ verdict: failed
//@ fn-failed: branch
//@ fixed-by: trusted_assertion_entry_refusal (the trusted fact is assumed at entry only where entry and program point agree)
//@ teeth: measured — before the fix `branch verified ✓` on the false contract (exit 2 only through `assumed=1`); after it `not assumed (a branch, call, assertion or drop precedes it)` and `branch FAILED ✗`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: branch(false, 5) returns 5. Only the `b` branch trusts `x == 0`.
#[ensures(result == 0i32)]
pub fn branch(b: bool, x: i32) -> i32 {
    if b {
        #[trusted]
        proof_assert! { x == 0i32 };
        x
    } else {
        x
    }
}
