//@ expect: reject
//@ mechanism: compound single-field struct W(Vec) built by aggregate and passed to a callee whose contract projects w.0
//@ accept-means: the callee postcondition was instantiated on a term other than the pushed vector
//@ teeth: verified (false accept) at wp-s11 1d1d3e5; rejected on wp-campaign 31addb5 (sort conflict / counterexample); refused by the compound single-field aggregate guard (25a0223)
//@ also-verified: callee
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W(pub Vec<u64>);

#[ensures(result@ == w.0@.len())]
pub fn callee(w: W) -> usize {
    w.0.len()
}

#[requires(w.0@.len() < 100)]
#[ensures(result@ == w.0@.len())]
pub fn caller(w: W) -> usize {
    let mut v = w.0;
    v.push(7);
    callee(W(v))
}
