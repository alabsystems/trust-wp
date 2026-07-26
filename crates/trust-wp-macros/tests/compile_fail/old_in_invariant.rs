// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `old()` cannot be used in #[invariant]
//!
//! Loop invariants are checked at each iteration. The `old()` form captures
//! function entry state, which isn't useful for iteration-by-iteration invariants.
//!
//! Issue: #212 (bug fix), #213 (test)

use trust_wp_macros::invariant;

// ERROR: `old()` can only be used in #[ensures] postconditions
#[invariant(i <= old(n))]
fn bad_old_invariant(n: i32) -> i32 {
    let mut i = 0;
    while i < n { i += 1; }
    i
}

fn main() {}
