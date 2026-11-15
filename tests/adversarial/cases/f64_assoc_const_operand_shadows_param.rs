//@ expect: reject
//@ mechanism: an associated constant used directly as a float operand (`f64::EPSILON`, `f64::MAX`) is not
//@ mechanism: evaluated on the operator path, so the operator is untranslated; D-215 names this and
//@ mechanism: says the assignment is havocked. It is havocked only for a fresh name: `on_assign_local`
//@ mechanism: binds the destination to `Var(<source name>)`, and `let x = x + f64::EPSILON` shadows a
//@ mechanism: parameter `x`, so the result is read as the parameter. The float spelling of
//@ mechanism: untranslated_local_shares_shadowed_symbol_in_postcondition.rs.
//@ accept-means: `add_epsilon(1.0)` returns `1.0000000000000002` and `double_max(0.0)` returns infinity;
//@ accept-means: an accept claims each returns its argument.
//@ fixed-by: OPEN — committed RED rather than hidden; closed with
//@ fixed-by: untranslated_local_shares_shadowed_symbol_in_postcondition.rs.
//@ teeth: ACCEPTED when committed (`add_epsilon verified`, `double_max verified`), and
//@ teeth: on the campaign tip before D-215.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == x)]
pub fn add_epsilon(x: f64) -> f64 {
    let x = x + f64::EPSILON;
    x
}

#[ensures(result == x)]
pub fn double_max(x: f64) -> f64 {
    let x = f64::MAX * 2.0;
    x
}
