// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: Creusot `^` (final/prophecy) syntax should be accepted
//! in pearlite! expressions after #2009 unified preprocessing.
//!
//! Previously `pearlite!(^x >= 0)` failed because pearlite! only applied
//! @ transforms (and only conditionally), not ^ or int-suffix transforms.

#![allow(unexpected_cfgs, dead_code, unused_variables)]

use trust_wp_macros::pearlite;

/// Stub for `final_value(expr)` — the ^ prefix transform rewrites `^x` to `final_value(x)`.
fn final_value<T>(x: T) -> T {
    x
}

fn main() {
    let x = 42i32;

    // AC3: pearlite!(^x >= 0) should compile (^ transform applied)
    // The ^ is preprocessed to final_value() during validation; the expansion
    // under cfg(not(trust_wp)) is just `true`, so final_value doesn't need to
    // be called at runtime.
    let _result: bool = pearlite!(^x >= 0);
}
