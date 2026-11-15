//@ expect: verify
//@ mechanism: the twin of destructured_mut_ref_requires_owed_at_call whose caller establishes the
//@ mechanism: callee's precondition over the argument it passes: `*x < 50` gives `*x < 100`.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control; refused at the head D-179 amends (the callee's `requires` was
//@ teeth: replaced by a refusal, so every call owed `false`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*p < 100i32 && *p > -100i32)]
pub fn g((p, _q): (&mut i32, &mut i32)) {
    *p += 1;
}

#[requires(*x < 50i32 && *x > -50i32)]
#[ensures(true)]
pub fn caller(x: &mut i32, y: &mut i32) {
    g((x, y));
}
