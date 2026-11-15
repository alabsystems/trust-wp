//@ expect: verify
//@ mechanism: the pre-Creusot spelling of a push's length, `v@.len() == old(v@.len()) + 1`: the
//@ mechanism: unwrapped `v@` is the value `v` is left with and `old(..)` reads the entry value, so
//@ mechanism: the clause states one push. The program of the simple_examples fixture's
//@ mechanism: `vec_push_len`, whose e2e pin now expects `verified`; its false twin is
//@ mechanism: vec_push_len_old_spelling_claims_two.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (control; `push_one verified` on the campaign head, and the twin FAILED)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(v@.len() == old(v@.len()) + 1)]
pub fn push_one(v: &mut Vec<i32>, val: i32) {
    v.push(val);
}
