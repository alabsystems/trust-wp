//@ expect: reject
//@ mechanism: a user callee's postcondition proved its own precondition (flat call effects)
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: `popu(&mut v)` verified with no length fact; `popu`'s ensures entailed its requires.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[trusted]
#[requires(v@.len() > 0)]
#[ensures((^v)@.len() == v@.len() - 1)]
pub fn popu(v: &mut Vec<u8>) {
    v.pop();
}

#[ensures(true)]
pub fn c(mut v: Vec<u8>) {
    popu(&mut v)
}
