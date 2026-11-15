//@ expect: reject
//@ mechanism: the false sibling of program_ensures_match_of_call_results_past_loop_control.rs: `let a =
//@ mechanism: match k { 0 => small(), 1 => medium(), _ => 0 }` returned past an annotated loop under
//@ mechanism: `ensures(result@ < 10)`. The arms whose value is `a`'s own call result state no loop-entry
//@ mechanism: value (D-244); `medium`'s postcondition allows 15.
//@ accept-means: a function that returns 15 is credited with returning less than 10.
//@ WHY IT IS FALSE: `go(1, 0)` returns 15.
//@ also-verified: small, medium
//@ teeth: rejected with D-243 and with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ < 10)]
pub fn small() -> u32 { 3 }

#[ensures(result@ < 20)]
pub fn medium() -> u32 { 15 }

#[requires(n@ < 100)]
#[ensures(result@ < 10)]
pub fn go(k: u8, n: u32) -> u32 {
    let a = match k { 0 => small(), 1 => medium(), _ => 0u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n { i += 1; }
    a
}
