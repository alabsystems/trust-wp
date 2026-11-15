//@ expect: reject
//@ mechanism: `a == a` over a value of an opaque return type (`fn hide(x: f64) -> impl PartialEq`)
//@ mechanism: calls `PartialEq::eq` with the opaque type as `Self`. D-215 withdraws the builtin
//@ mechanism: comparison contract (`result == (self@ == rhs@)`, logical equality) from a comparison
//@ mechanism: method whose type arguments carry a float, but it asked the call site's arguments as
//@ mechanism: written, where the opaque type names no float, and then the resolved method's own
//@ mechanism: arguments, which for the primitive `impl PartialEq for f64` are empty. So the logical
//@ mechanism: contract ran and `a == a` was proved, and `a != a` refuted, at every `x`. The opaque
//@ mechanism: twin of f64_partial_eq_method_reflexive.rs and f64_partial_ne_method_irreflexive.rs.
//@ accept-means: `opaque_eq_reflexive(f64::NAN)` returns `false` and `opaque_ne_irreflexive(f64::NAN)`
//@ accept-means: returns `true`; an accept claims the opposite (and the same of `f32::NAN`).
//@ also-verified: hide, hide32
//@ fixed-by: D-215
//@ teeth: ACCEPTED when committed (`opaque_eq_reflexive`, `opaque_ne_irreflexive` and
//@ teeth: `opaque_eq_reflexive_f32` each verified); each `unknown` once the guard asks the arguments
//@ teeth: as they resolve.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn hide(x: f64) -> impl PartialEq + Copy {
    x
}

#[ensures(true)]
pub fn hide32(x: f32) -> impl PartialEq + Copy {
    x
}

#[ensures(result)]
pub fn opaque_eq_reflexive(x: f64) -> bool {
    let a = hide(x);
    a == a
}

#[ensures(!result)]
pub fn opaque_ne_irreflexive(x: f64) -> bool {
    let a = hide(x);
    a != a
}

#[ensures(result)]
pub fn opaque_eq_reflexive_f32(x: f32) -> bool {
    let a = hide32(x);
    a == a
}
