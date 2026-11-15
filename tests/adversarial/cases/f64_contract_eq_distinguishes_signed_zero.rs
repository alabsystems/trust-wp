//@ expect: reject
//@ mechanism: a contract `==` is logical equality (Pearlite's `=`, which Creusot reads over Why3's
//@ mechanism: IEEE floats as equality of values), under which `-0.0` and `0.0` are different values: they
//@ mechanism: compare equal under IEEE-754 `==` but `1.0 / -0.0 == -inf`. Reals have one zero.
//@ accept-means: `neg_zero()` returns `-0.0`; an accept claims the value returned is `0.0`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`neg_zero verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 0.0)]
pub fn neg_zero() -> f64 {
    -0.0
}
