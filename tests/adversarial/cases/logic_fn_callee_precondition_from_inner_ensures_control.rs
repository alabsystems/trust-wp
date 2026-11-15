//@ expect: verify
//@ mechanism: control: the outer call's precondition follows from the inner call's `ensures` (Creusot's vcgen `Call`: `requires && (ensures ==> k(call))`); the goal is proved with the callee's spec axiom, which holds where the inner call's own precondition does.
//@ accept-means: n/a (control) — `pos(y) > 0` holds wherever `y > 0` does.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
#[ensures(result > 0)]
pub fn pos(x: Int) -> Int {
    x
}

#[logic]
#[requires(y > 0)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    pos(pos(y))
}
