//@ expect: reject
//@ mechanism: `FSet::interval(i, j)` is Why3 `FsetInt.interval`, the half-open `[i, j)`; its membership axiom must not also admit `j`
//@ accept-means: the interval axiom was encoded closed (or not at all and something else proved the law), so `interval(0, 1)` was proved to contain 1
//@ teeth: none demonstrated — measured `unknown`/timeout, never verified; the case guards the membership theory against an encoding that would prove a false law
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{logic::FSet, prelude::*};

// WRONG: interval(0, 1) does not contain 1.
#[ensures(forall<i, j, k> FSet::interval(i, j).contains(k) == (i <= k && k <= j))]
pub fn interval_closed() {}
