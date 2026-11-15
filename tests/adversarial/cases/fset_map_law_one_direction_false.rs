//@ expect: reject
//@ mechanism: the quantified-iff split verifies `forall v. L == R` as `L ==> R` and `R ==> L`; this law's forward direction holds and its backward one does not, so the whole must be refused
//@ accept-means: one direction of a split equivalence was credited for both
//@ teeth: none demonstrated — measured `unknown`/timeout, never verified; the case guards the membership theory against an encoding that would prove a false law
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{
    logic::{FSet, Mapping},
    prelude::*,
};

// WRONG backward: a non-empty xs need not map anything to a given y.
// The forward direction (y in the image => xs is non-empty) is true.
#[ensures(forall<xs: FSet<T>, f: Mapping<T, U>, y: U> xs.map(f).contains(y) == exists<x: T> xs.contains(x))]
pub fn image_iff_nonempty<T, U>() {}
