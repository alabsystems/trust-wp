//@ expect: reject
//@ mechanism: `s.map(f)` is Why3 `Fset.map`: `mem y (map f s) <-> exists x. mem x s /\ y = f x`; a law that forgets `f` is false
//@ accept-means: `map` was read as the identity on its receiver
//@ teeth: none demonstrated — measured `unknown`/timeout, never verified; the case guards the membership theory against an encoding that would prove a false law
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{
    logic::{FSet, Mapping},
    prelude::*,
};

// WRONG: map with a non-identity f moves elements.
#[ensures(forall<xs: FSet<T>, f: Mapping<T, T>, y: T> xs.map(f).contains(y) == xs.contains(y))]
pub fn map_identity<T>() {}
