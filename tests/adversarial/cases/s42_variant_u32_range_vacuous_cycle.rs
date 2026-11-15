//@ expect: reject
//@ verdict: error
//@ refused-with: variant obligation returned unknown: vacuous proof: base assertions are UNSAT without the negated postcondition
//@ mechanism: u32 range facts made the variant edge vacuous (x@ > u32::MAX) while k's defining axiom stayed unguarded over Int
//@ fixed-by: s42 variant-range-facts-v2
//@ accept-means: the u32 range guard on the defining axiom is gone
//@ timeout: 300
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn k(x: u32) -> Int {
    pearlite! { if x@ > 4294967295 { k(x) + 1 } else { 0 } }
}

#[ensures(k(4294967295u32 + 1u32) == 5)]
pub fn two() {}
