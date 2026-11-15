//@ expect: verify
//@ mechanism: a destructuring parameter binds `&mut`s: `p` of `(p, q): (&mut i32, &mut i32)`. Its
//@ mechanism: `requires` is read at entry through the parameter's projection, the term `*t.0` of a
//@ mechanism: tuple parameter `t` is (D-179), and a postcondition that names no binding is proved.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control. Refused at the head D-179 amends: D-177 refused every clause
//@ teeth: over a binding whose type holds a reference, the `requires` included, so nothing of this
//@ teeth: shape verified (the generated oracle's destructured host had no verified case).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*p < 100i32 && *p > -100i32)]
#[ensures((0i32 < 1i32) == (1i32 > 0i32))]
pub fn g((p, _q): (&mut i32, &mut i32)) {
    *p += 1;
}
