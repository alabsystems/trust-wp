//@ expect: reject
//@ verdict: error
//@ refused-with: variant obligation returned unknown: vacuous proof: base assertions are UNSAT without the negated postcondition
//@ mechanism: u8 range facts made the variant edge vacuous (x@ > 300) while k's defining axiom stayed unguarded over Int
//@ fixed-by: s42 variant-range-facts-v2
//@ accept-means: k(400) = k(400) + 1 was usable outside u8: the defining axiom is not range-guarded again
//@ timeout: 300
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn k(x: u8) -> Int {
    pearlite! { if x@ > 300 { k(x) + 1 } else { 0 } }
}

#[ensures(k(200u8 + 200u8) == 5)]
pub fn two() {}
