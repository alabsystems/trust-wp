//@ expect: verify
//@ mechanism: control for u128_literal_suffix_value_false, which differs in one literal: a clause
//@ mechanism: holding `u128`-suffixed literals and no operator is parsed and its values read (the
//@ mechanism: u128_literal_suffix_contract pair's arithmetic is refused under D-232).
//@ WHY THE CONTRACT IS TRUE: inc(5) returns 6.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x == 5u128)]
#[ensures(result == 6u128)]
pub fn inc(x: u128) -> u128 {
    x + 1
}
