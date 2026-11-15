//@ expect: reject
//@ mechanism: a LOCAL contract-less callee that can PANIC must not be treated as total, and its result must stay unconstrained
//@ accept-means: the caller was credited with a claim about the result of a call whose body it never read — and whose `assert!` is posed nowhere (the panic-site lane does not reach contract-less items)
//@ fixed-by: n/a — s80 FALSE-ACCEPT gate
//@ teeth: rejected on wp-s80 base and after the s80 fix. Prospective for routes (b)/(c).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// Contract-less, LOCAL, panics on the odd path.
fn checked_half(x: u32) -> u32 {
    assert!(x % 2 == 0, "odd");
    x / 2
}

// WRONG: caller(8) returns 4, not 8.
#[requires(a@ == 8u32@)]
#[ensures(result@ == a@)]
pub fn caller(a: u32) -> u32 {
    checked_half(a)
}
