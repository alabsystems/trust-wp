//@ expect: verify
//@ mechanism: the isolating control for closure_callee_requires_through_iterator_map_uncharged: the
//@ mechanism: SAME closure handed to the SAME `Iterator::map`, with the call to `needs_nonzero`
//@ mechanism: guarded by `x != 0` inside the closure. Creusot proves it: the closure's
//@ mechanism: precondition (its body's weakest precondition) is `true`. A fix that charges the
//@ mechanism: combinator's `f.precondition` must keep this verifying.
//@ accept-means: n/a (control) — no call leaves `needs_nonzero`'s precondition.
//@ fixed-by: n/a (control)
//@ teeth: control — verifies. Its RED twin differs only in the guard.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ != 0)]
#[ensures(result@ == 10 / x@)]
pub fn needs_nonzero(x: u32) -> u32 {
    10 / x
}

pub fn hop(v: &[u32]) -> Option<u32> {
    v.iter().map(|&x| if x != 0 { needs_nonzero(x) } else { 0 }).next()
}
