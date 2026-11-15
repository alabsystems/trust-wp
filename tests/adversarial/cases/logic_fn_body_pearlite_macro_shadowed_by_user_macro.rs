//@ expect: reject
//@ verdict: error
//@ refused-with: a macro `pearlite!` defined by the crate
//@ mechanism: the `pearlite!` spelling of logic_fn_body_seq_macro_shadowed_by_user_macro.rs: the crate's own `macro_rules! pearlite` shadows the prelude's, and a logic body is `pearlite! { 1 }`. rustc expands the crate's macro, here `0`; the contract parser treats `pearlite!` as transparent and reads the body as `1`, and nothing checks which macro the name denotes. Found probing sideways from D-136.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ accept-means: a logic function is credited with the value of a body its macro does not produce, and the crate exits 0.
//@ WHY IT IS FALSE: `pearlite! { 1 }` expands to `Int::from(0)`, so `caller()` is `0`, not `1`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: creusot_test::caller verified ✓`. The control is logic_fn_body_pearlite_macro_shadowed_by_user_macro_control.rs, which differs in the crate's macro alone and verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

macro_rules! pearlite {
    ($($t:tt)*) => {
        Int::from(0)
    };
}

#[logic]
#[ensures(result == 1)]
pub fn caller() -> Int {
    pearlite! { 1 }
}
