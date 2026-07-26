#![allow(unexpected_cfgs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression for #1500: projected overwrite of a sub-structure must invalidate
//! stale facts for nested projected paths from the previous value.
//!
//! Sequence:
//! - `pair.0.1 = 10` introduces projected-write fact for nested path
//! - `pair.0 = new_head` overwrites the parent path with a fresh value
//!
//! Correct behavior: `proof_assert!(pair.0.1@ == 10)` must fail.

use trust_wp::proof_assert;

fn projected_substruct_overwrite_should_fail(mut pair: ((i32, i32), i32), new_head: (i32, i32)) {
    (pair.0).1 = 10;
    pair.0 = new_head;

    // If nested stale facts survive parent-path overwrite, this can verify
    // vacuously. Sound extraction must reject it.
    proof_assert!((pair.0).1@ == 10);
    let _ = pair;
}

fn main() {
    projected_substruct_overwrite_should_fail(((0, 0), 0), (7, 20));
}
