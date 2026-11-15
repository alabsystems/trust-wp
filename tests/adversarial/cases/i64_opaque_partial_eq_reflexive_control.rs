//@ expect: verify
//@ mechanism: the isolating twin of f64_opaque_partial_eq_reflexive_despite_nan.rs: the same opaque
//@ mechanism: return type over `i64`, where `PartialEq` is logical equality, keeps the builtin contract
//@ mechanism: once the opaque type is revealed; only a float-carrying one loses it.
//@ accept-means: n/a (control) — `a == a` holds, and `a != a` fails, for every integer.
//@ fixed-by: n/a (control)
//@ teeth: verified before the guard asked the arguments as they resolve, and after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn hide(x: i64) -> impl PartialEq + Copy {
    x
}

#[ensures(result)]
pub fn opaque_eq_reflexive(x: i64) -> bool {
    let a = hide(x);
    a == a
}

#[ensures(!result)]
pub fn opaque_ne_irreflexive(x: i64) -> bool {
    let a = hide(x);
    a != a
}
