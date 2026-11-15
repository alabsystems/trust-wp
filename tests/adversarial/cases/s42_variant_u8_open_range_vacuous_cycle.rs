//@ expect: reject
//@ verdict: error
//@ refused-with: variant obligation returned unknown: vacuous proof: base assertions are UNSAT without the negated postcondition
//@ mechanism: machine-int range facts made a variant decrease vacuous while the OPEN defining equation stayed usable outside the type range
//@ fixed-by: s42 v2 (range requires guard every #[variant] logic fn definition and unfolding)
//@ accept-means: an open logic fn's defining equation was unfolded at an out-of-range argument (k(400) = k(400) + 1)
//@
//@ WHY THE CONTRACT IS FALSE: Creusot rejects k's variant (x > 300 is reachable in the Int model of
//@ `200u8 + 200u8`); trust-wp must not derive k(400) == 5 from a range-vacuous decrease proof.
//@ teeth: open-mode twin of s42_variant_u8_range_vacuous_cycle; exercises the open-logic unfold paths.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
#[variant(x)]
pub fn k(x: u8) -> Int {
    pearlite! { if x@ > 300 { k(x) + 1 } else { 0 } }
}

#[ensures(k(200u8 + 200u8) == 5)]
pub fn two() {}
