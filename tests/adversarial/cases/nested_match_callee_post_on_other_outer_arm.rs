//@ expect: reject
//@ mechanism: nested arm premises (D-169): every arm of the inner `match k` calls `below(x)`, so the inner
//@ mechanism: edges cover every execution of the outer `flag` arm, and the inner scoping alone leaves
//@ mechanism: `x@ < 100` derivable wherever `flag` holds. The outer arm must scope those premises again by
//@ mechanism: `flag`; unscoped, `ensures(x@ < 100)` follows on the `!flag` path.
//@ accept-means: a contract is verified from callee postconditions on an execution that calls neither,
//@ accept-means: and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, false, 0)` returns with `x == 200`.
//@ teeth: ACCEPTED at the campaign tip; rejected with D-169.
//@ verdict: failed
//@ fn-failed: f
//@ also-verified: below
//@ fixed-by: D-169 (each premise an arm walk records is scoped to that arm's edge).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100 && result == x)]
pub fn below(x: u32) -> u32 {
    #[invariant(true)]
    while x >= 100 {}
    x
}

#[ensures(x@ < 100)]
pub fn f(x: u32, flag: bool, k: u8) {
    if flag {
        match k {
            0 => { below(x); }
            _ => { below(x); }
        }
    }
}
