#![allow(unexpected_cfgs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression for projected-write fact invalidation:
//! whole-local reassignment must invalidate earlier projected-write facts.
//!
//! Sequence:
//! - `pair.0 = 5` introduces projected-write fact `pair.0 == 5`
//! - `pair = (7,)` overwrites the entire base local
//!
//! Correct behavior: `proof_assert!(pair.0@ == 5)` must fail.

use trust_wp::proof_assert;

fn projected_write_then_whole_reassign_should_fail() {
    let mut pair = (0_i32,);
    pair.0 = 5;
    pair = (7_i32,);

    // If stale projected-write facts survive whole-local reassignment, this can
    // verify vacuously. Sound extraction must reject it.
    proof_assert!(pair.0@ == 5);
    let _ = pair;
}

fn main() {
    projected_write_then_whole_reassign_should_fail();
}
