//@ expect: reject
//@ also-verified: g
//@ mechanism: a callee writes through a `&mut` its destructuring parameter binds, and states nothing
//@ mechanism: about it. The caller passes its own `&mut` inside the tuple argument, so the call may
//@ mechanism: change `*x`: read as unchanged, the caller is credited with the entry value.
//@ accept-means: a write through a `&mut` handed to a callee inside a tuple argument was not seen by
//@ accept-means: the caller.
//@ WHY THE CONTRACT IS FALSE: `g` increments `*p`, which is `*x`, so `*x` after the call is
//@ WHY THE CONTRACT IS FALSE: `old(*x) + 1`.
//@ fixed-by: n/a — coverage of the call lane D-179 opens to a destructured `&mut` callee: the caller's
//@ fixed-by: `*x` is unknown after the call, as with a tuple parameter.
//@ teeth: unknown (`caller unknown`) with `g verified` at D-179's head; the tuple-parameter spelling of
//@ teeth: `g` is unknown the same way. At the head D-179 amends `g`'s `requires` was refused and the
//@ teeth: call owed `false`, so the case was rejected for that reason instead.
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
#[ensures(*x == old(*x))]
pub fn caller(x: &mut i32, y: &mut i32) {
    g((x, y));
}
