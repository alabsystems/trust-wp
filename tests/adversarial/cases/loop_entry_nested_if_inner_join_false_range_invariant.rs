//@ expect: reject
//@ mechanism: the false sibling of loop_entry_nested_if_inner_join_range_invariant_control.rs: `if c { if d
//@ mechanism: { small() } else { 30 } } else { 4 }` initiates `a@ < 10`. The inner join's arms must not be
//@ mechanism: read as one.
//@ accept-means: a loop invariant is initiated from one inner arm's callee promise.
//@ WHY IT IS FALSE: `go(true, false, 1)` enters the loop with `a == 30`.
//@ also-verified: small
//@ teeth: rejected with D-243 and with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ < 10)]
pub fn small() -> u32 { 3 }

#[requires(n@ < 100)]
pub fn go(c: bool, d: bool, n: u32) {
    let a = if c { if d { small() } else { 30u32 } } else { 4u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@ && a@ < 10)]
    while i < n { i += 1; }
}
