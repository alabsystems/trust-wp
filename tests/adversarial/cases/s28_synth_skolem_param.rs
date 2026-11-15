//@ expect: reject
//@ mechanism: the negated universal goal skolemized `forall<i>` to Var("sk_i"), the same symbol as a parameter named `sk_i`; skolems are now `sk$i`.
//@ fixed-by: wp-s28 (trust-wp-ay skolem names in the `$` namespace)
//@ accept-means: g proved every u32 equals its parameter.
//@ teeth: exit-0 false accept on 22198c14 (rv8/sk1); renamed parameter (sk1n) FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: not every i equals the parameter.
#[ensures(forall<i: u32> i == sk_i)]
pub fn g(sk_i: u32) {}
