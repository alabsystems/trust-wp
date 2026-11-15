// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN: twin of `should_fail_assert_contractless` whose `assert!` holds on
//! every path. The switch lane states the unreachability of the assertion's
//! panic arm as a goal and records the edge it charged, so the clause-free
//! cap does not walk it and the body verifies instead of being capped.

pub fn assert_guarded(x: u8) -> u8 {
    if x < 3 {
        assert!(x < 5);
    }
    x
}

fn main() {}
