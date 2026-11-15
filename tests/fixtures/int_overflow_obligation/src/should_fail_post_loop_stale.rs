// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED (stale value): a loop WITHOUT an invariant increments `i`; the
//! `i + 1` after the loop must be checked against the loop-exit value of
//! `i` (unknown: may be 255), never against its pre-loop value `0`.

use trust_wp::ensures;

#[ensures(true)]
pub fn after_loop(n: u8) -> u8 {
    let mut i: u8 = 0;
    while i < n {
        i += 1;
    }
    i + 1
}

fn main() {}
