//@ expect: verify
//@ mechanism: over-refusal control — the caller's claim does not rest on the contract-less `10 / y` callee's result
//@ xfail: the local opaque call is owed `requires(false)`, so every caller is unprovable today.
//@ teeth: n/a — over-refusal control. An XPASS here is a WARNING, not a win: it means a caller of a fn whose division-by-zero obligation is posed nowhere was credited. Read with `x_contractless_div_by_zero`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

fn div10(y: i32) -> i32 {
    10 / y
}

// TRUE: caller_ok(y) returns y for every y.
#[ensures(result@ == y@)]
pub fn caller_ok(y: i32) -> i32 {
    let _ignored = div10(2);
    y
}
