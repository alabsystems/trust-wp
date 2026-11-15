//@ expect: reject
//@ mechanism: a `u128`-suffixed literal in a clause is read at its value, not dropped or clamped:
//@ mechanism: the twin of u128_literal_suffix_contract_control with `2u128` for `1u128`.
//@ accept-means: the literal suffix range admitted the clause but its value was lost.
//@ WHY THE CONTRACT IS FALSE: `inc(0)` returns 1, and the clause claims 2.
//@ verdict: unknown
//@ refused-with: wraps at 128 bits
//@ teeth: the pair differs in one literal and the control verifies; before the fix both were
//@ teeth: compile errors (the suffix range panicked), so the refutation is the parser reading 2.
//@ teeth: D-232 refuses the clause's `+` on `u128` (the oracle's add wraps at 128 bits), so the
//@ teeth: literal's value is read by u128_literal_suffix_value_false.rs, which has no operator.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
#[ensures(result == x + 2u128)]
pub fn inc(x: u128) -> u128 {
    x + 1
}
