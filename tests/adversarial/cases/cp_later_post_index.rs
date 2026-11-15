//@ expect: reject
//@ mechanism: a LATER call's postcondition (`v@.len() > 0`) must not discharge an EARLIER `v[0]` bounds precondition
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: f verified; it panics for an empty vector (the helper is trusted, so the crate exit is 2 either way: fn-failed pins f).
//@ fn-failed: f
//@ teeth: f verified on HEAD 5780c31e and base 853ad732 (review probe r_later_post2).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
#[trusted]
#[ensures(v@.len() > 0)]
pub fn nonempty(v: &Vec<u8>) { loop {} }
#[ensures(true)]
pub fn f(v: &Vec<u8>) -> u8 {
    let x = v[0];
    nonempty(v);
    x
}
