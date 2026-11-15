//@ expect: reject
//@ mechanism: D-215 left every operator and cast over an `f16` untranslated, and `on_assign_local` bound a
//@ mechanism: destination whose right-hand side it cannot translate to `Var(<source name>)`: a local that
//@ mechanism: shadows a parameter (`let a = h as u32;`, `let x = h as f32;`) was then the parameter's symbol, so
//@ mechanism: `#[ensures(result == a)]` read the returned local as the parameter, the hole of
//@ mechanism: untranslated_local_shares_shadowed_symbol_in_postcondition.rs. D-169 binds such an assignment to
//@ mechanism: a symbol of its site, and D-217 translates the cast as an uninterpreted function of `h`, so
//@ mechanism: neither spelling reaches the hole. An `f32` source in the same place is an IEEE conversion.
//@ accept-means: `to_int(0, 2.0)` returns `2` and `widen(0.0, 2.0)` returns `2.0`; an accept claims each
//@ accept-means: returns its first argument.
//@ fixed-by: D-169 (the site symbol) and D-217 (the cast translated)
//@ teeth: ACCEPTED when committed (`to_int verified`, `widen verified`); rejected (`failed`) by the campaign
//@ teeth: tip before D-215, which lowered the cast over the reals, by the merged tip with D-169, and under
//@ teeth: D-217 (`to_int` FAILED, `widen` unknown).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(f16)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == a)]
pub fn to_int(a: u32, h: f16) -> u32 {
    let a = h as u32;
    a
}

#[ensures(result == x)]
pub fn widen(x: f32, h: f16) -> f32 {
    let x = h as f32;
    x
}
