//@ expect: reject
//@ mechanism: a `u128`-suffixed literal in a clause with no operator is read at its value, not
//@ mechanism: dropped or clamped: the twin of u128_literal_suffix_value_control with `7u128`.
//@ accept-means: the literal suffix range admitted the clause but its value was lost.
//@ WHY THE CONTRACT IS FALSE: inc(5) returns 6, and the clause claims 7.
//@ verdict: failed
//@ fn-failed: inc
//@ teeth: UNVERIFIED: written beside D-232, which refuses the u128_literal_suffix_contract pair's
//@ teeth: `+`; the pair differs in one literal and the control verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x == 5u128)]
#[ensures(result == 7u128)]
pub fn inc(x: u128) -> u128 {
    x + 1
}
