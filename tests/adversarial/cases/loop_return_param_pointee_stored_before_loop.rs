//@ expect: reject
//@ mechanism: a store through a `&mut` parameter BEFORE the loop, which the loop never touches: the
//@ mechanism: function-level continuation read the returned `*a` at its entry value, since the
//@ mechanism: block-scoped walks a loop function's obligations are rebuilt from dropped the primary
//@ mechanism: walk's return sink for a read after a store.
//@ accept-means: `f` returns 7, so `result@ == 0` is FALSE, and trust-wp proved it.
//@ fixed-by: D-223 (a loop function keeps the return sink's `false`)
//@ teeth: ACCEPTED at exit 0 (`f verified`) before D-223.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
#[ensures(result@ == 0)]
pub fn f(a: &mut u32) -> u32 {
    *a = 7;
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
    *a
}
