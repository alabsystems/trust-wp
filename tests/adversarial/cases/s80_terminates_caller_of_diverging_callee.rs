//@ expect: reject
//@ mechanism: a `#[check(terminates)]` caller of a LOCAL contract-less NON-TERMINATING callee must not be credited — an empty contract means the callee promises nothing, not that it returns
//@ accept-means: the termination lane treated an unannotated local callee as total; `spin(0)` never returns, so `caller` never returns either
//@ fixed-by: n/a — s80 FALSE-ACCEPT gate
//@ verdict: error
//@ refused-with: termination check failed: `caller`: #[check(terminates)] function calls `spin` which is not marked #[check(terminates)]
//@ teeth: rejected on wp-s80 base and after the s80 fix. Prospective for routes (b)/(c), and for any future widening of the termination lane's call-graph treatment.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// Contract-less, LOCAL, and it never returns.
fn spin(n: i32) -> i32 {
    spin(n)
}

// WRONG: `caller()` is declared terminating but calls `spin`, which diverges.
#[check(terminates)]
#[ensures(result@ == 1i32@)]
pub fn caller() -> i32 {
    let _ = spin(0);
    1
}
