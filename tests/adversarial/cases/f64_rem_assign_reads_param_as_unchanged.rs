//@ expect: reject
//@ mechanism: `on_assign_local` binds a destination whose right-hand side it leaves untranslated to
//@ mechanism: `Var(<source name>)`, and for a parameter that name IS the parameter's entry symbol. A float
//@ mechanism: `%` left untranslated (Rust's remainder truncates, SMT-LIB's `fp.rem` rounds, so it has no
//@ mechanism: IEEE operation) reaches that fallback: after `a %= y`, `a = a % y` or `let a = a % y` the
//@ mechanism: returned `a` is read as the value `a` had on entry, and `result == a` holds by reflexivity.
//@ mechanism: D-215 reads `%` as an uninterpreted function of its operands, so it never takes the fallback.
//@ accept-means: `rem_assign(7.0, 5.0)` returns `2.0`; an accept claims it returns `7.0`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED while D-215 left `%` untranslated (`rem_assign`, `rem_reassign` and `rem_shadows_param`
//@ teeth: each verified); `unknown` on the campaign tip before D-215, which translated the remainder over
//@ teeth: the reals; each FAILED with `%` an uninterpreted function.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == a)]
pub fn rem_assign(mut a: f64, y: f64) -> f64 {
    a %= y;
    a
}

#[ensures(result == a)]
pub fn rem_reassign(mut a: f64, y: f64) -> f64 {
    a = a % y;
    a
}

#[ensures(result == a)]
pub fn rem_shadows_param(a: f64, y: f64) -> f64 {
    let a = a % y;
    a
}
