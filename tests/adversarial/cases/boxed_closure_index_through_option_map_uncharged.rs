//@ expect: reject
//@ mechanism: the store-only constructors of D-118 must not hide the closure they store: a bounds
//@ mechanism: check in a closure moved into a `Box` handed to `Option::map`, and in a closure held by
//@ mechanism: an `Rc` or `Arc` that an escaping closure calls. `Box::new`, `Rc::new` and `Arc::new`
//@ mechanism: are no hand-off, so the closure must be found again where the value that holds it
//@ mechanism: goes: through `Box`'s type argument into `map`, and through the escaping closure's
//@ mechanism: capture.
//@ accept-means: a host is reported `verified` although `via_box(Some(0), &[])` (and its siblings)
//@ accept-means: index an empty slice inside the closure `Option::map` calls.
//@ WHY THE CONTRACT IS FALSE: each host indexes `w` at an index the caller chooses, unguarded.
//@ fixed-by: D-118: the closure is a target, verified under `requires true`, and each host rests on
//@ fixed-by: its verdict.
//@ teeth: ACCEPTED, exit 0, every host `verified`, on the binary before D-118. After it each host's
//@ teeth: credit is withdrawn on its closure's refuted bounds check.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::rc::Rc;
use std::sync::Arc;

#[ensures(true)]
pub fn via_box(o: Option<usize>, w: &[u32]) -> Option<u32> {
    o.map(Box::new(|j: usize| w[j]))
}

#[ensures(true)]
pub fn via_rc(o: Option<usize>, w: &[u32]) -> Option<u32> {
    let f = Rc::new(|j: usize| w[j]);
    o.map(|j| f(j))
}

#[ensures(true)]
pub fn via_arc(o: Option<usize>, w: &'static [u32]) -> Option<u32> {
    let f = Arc::new(move |j: usize| w[j]);
    o.map(move |j| f(j))
}
