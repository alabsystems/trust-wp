//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_next_power_of_two_overflow_panics, identical but for the
//@ mechanism: bound: 128 is `u8`'s largest power of two, the edge the precondition must admit.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ <= 128)]
#[ensures(true)]
pub fn f(x: u8) -> u8 {
    x.next_power_of_two()
}
