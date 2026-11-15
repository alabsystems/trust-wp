//@ expect: reject
//@ mechanism: unnesting a `&mut &mut T` into `&mut **x` leaves the reborrow's prophecy unconstrained — the equations tying `^inner` back to `^*x` and `^^x`, and so to the doubly-borrowed local, are never emitted, so the write through `inner` reaches nothing.
//@ accept-means: an ACCEPT proves the entry value of a doubly-borrowed local is still readable after a write through the unnested borrow — the prophecy chain is a free variable the goal may pick, so the encoding is wrong in BOTH directions and its true twin is refuted.
//@ fixed-by: 7bb3a696 — the resolver walks the unnesting hop by hop, and reading through an alias is not redirecting through it.
//@ teeth: CLOSED. The case now rejects and its control verifies, so the unnested borrow's write reaches the doubly-borrowed local in both directions.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn mirror2() {
    let mut v: i32 = 0;
    let mut r = &mut v;
    let x = &mut r;
    let inner: &mut i32 = &mut **x;
    *inner = 1;
    // FALSE: `*inner = 1` writes through the chain x -> r -> v, so v is 1 here.
    proof_assert!(v == 0);
}
