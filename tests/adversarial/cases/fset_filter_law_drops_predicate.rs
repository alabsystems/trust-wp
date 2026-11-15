//@ expect: reject
//@ mechanism: `s.filter(p)` is Why3 `Fset.filter`: membership is `mem x s /\ p x`; a law that forgets `p` is false
//@ accept-means: `filter` was read as the identity on its receiver
//@ teeth: none demonstrated — measured `unknown`/timeout, never verified; the case guards the membership theory against an encoding that would prove a false law
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{
    logic::{FSet, Mapping},
    prelude::*,
};

// WRONG: a predicate that rejects x removes it.
#[ensures(forall<xs: FSet<T>, f: Mapping<T, bool>, x: T> xs.filter(f).contains(x) == xs.contains(x))]
pub fn filter_identity<T>() {}
