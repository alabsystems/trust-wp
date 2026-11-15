//@ expect: verify
//@ mechanism: isolating twin of `fset_map_law_one_direction_false` — its true forward direction alone, so the reject case fails on the backward direction and nothing else
//@ xfail: ends `unknown (proof-trusted)`: ay's UNSAT through the Skolemized map axiom is not strictly certified
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{
    logic::{FSet, Mapping},
    prelude::*,
};

#[ensures(forall<xs: FSet<T>, f: Mapping<T, U>, y: U> xs.map(f).contains(y) ==> exists<x: T> xs.contains(x))]
pub fn image_nonempty<T, U>() {}
