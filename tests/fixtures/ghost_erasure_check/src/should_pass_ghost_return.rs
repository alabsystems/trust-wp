// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost erasure check: ghost-returning function that should PASS.
//!
//! Returning `Ghost<T>` from an ordinary function is allowed because the
//! runtime-erased carrier does not leak runtime-observable state. The real
//! erasure check is about control-flow dependence, covered separately by the
//! `should_fail_switchint` fixture.

use trust_wp_std::{ghost, ghost::Ghost};

/// Ghost-only computation returning `Ghost<T>` should be accepted.
#[allow(dead_code)]
pub fn returns_ghost_value() -> Ghost<i32> {
    let g = ghost! { 42 };
    g
}

fn main() {}
