#![allow(unexpected_cfgs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression for #1424: repeated projected writes must use last-write-wins.
//!
//! Before #1424, extraction retained both write facts:
//! - pair.0 == 5
//! - pair.0 == 7
//!
//! The contradictory assumptions made `proof_assert!(pair.0@ == 5)` vacuously
//! verify. Correct behavior is verification failure.

use trust_wp::proof_assert;

fn contradictory_projected_writes_should_fail() {
    let mut pair = (0_i32,);
    pair.0 = 5;
    let first_write = pair.0;
    pair.0 = 7;
    let _ = first_write;

    // With correct extraction, only `pair.0 == 7` is in scope here, so this fails.
    proof_assert!(pair.0@ == 5);
    let _ = pair;
}

fn main() {
    contradictory_projected_writes_should_fail();
}
