//@ expect: reject
//@ mechanism: a named constant used directly as a float operand is not evaluated on the float operator
//@ mechanism: path, so the operator is untranslated, and `on_assign_local` binds a destination it cannot
//@ mechanism: translate to `Var(<source name>)`: `let x = x + ONE` shadows the parameter `x` and is read
//@ mechanism: as the parameter. f64_assoc_const_operand_shadows_param.rs is the associated-constant
//@ mechanism: spelling (`f64::EPSILON`); these are a local `const` item, a `core::f64::consts` constant
//@ mechanism: and `f32::MAX`. The `i64` spelling with a local `const` is refused (`unknown`, a fail-closed
//@ mechanism: `false` injected for the construct).
//@ accept-means: `add_one(1.0)` returns `2.0`, `add_pi(0.0)` returns `PI` and `mul_max(2.0)` returns
//@ accept-means: infinity; an accept claims each returns its argument.
//@ fixed-by: OPEN — committed RED rather than hidden; closed with
//@ fixed-by: untranslated_local_shares_shadowed_symbol_in_postcondition.rs.
//@ teeth: ACCEPTED when committed (`add_one verified`, `add_pi verified`, `mul_max verified`), and on the
//@ teeth: campaign tip before D-215.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

const ONE: f64 = 1.0;

#[ensures(result == x)]
pub fn add_one(x: f64) -> f64 {
    let x = x + ONE;
    x
}

#[ensures(result == x)]
pub fn add_pi(x: f64) -> f64 {
    let x = x + std::f64::consts::PI;
    x
}

#[ensures(result == x)]
pub fn mul_max(x: f32) -> f32 {
    let x = x * f32::MAX;
    x
}
