//@ expect: reject
//@ mechanism: a trait's associated constant used directly as a float operand (`x + <S as K>::C`) is not
//@ mechanism: evaluated on the float operator path, so the operator is untranslated and the destination
//@ mechanism: is bound to its source name: `let x = x + <S as K>::C` shadows the parameter `x` and is read
//@ mechanism: as the parameter. The spelling of f64_assoc_const_operand_shadows_param.rs (an inherent
//@ mechanism: associated constant) and f64_const_item_operand_shadows_param.rs (a local `const`, a
//@ mechanism: `core::f64::consts` constant, `f32::MAX`) reached through an impl of a user trait, found
//@ mechanism: probing sideways from D-215. Over `i64` an untranslated operand reaches the overflow
//@ mechanism: check, which cannot be translated either, and the function is refused; a float operator
//@ mechanism: has no check to carry that refusal.
//@ accept-means: `add_assoc(1.0)` returns `2.0` and `mul_assoc_f32(2.0)` returns `6.0`; an accept claims
//@ accept-means: each returns its argument.
//@ fixed-by: OPEN — committed RED rather than hidden; closed with
//@ fixed-by: untranslated_local_shares_shadowed_symbol_in_postcondition.rs.
//@ teeth: ACCEPTED when committed (`add_assoc verified`, `mul_assoc_f32 verified`), and on the campaign
//@ teeth: tip before D-215.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait K {
    const C: f64;
    const C32: f32;
}

pub struct S;

impl K for S {
    const C: f64 = 1.0;
    const C32: f32 = 3.0;
}

#[ensures(result == x)]
pub fn add_assoc(x: f64) -> f64 {
    let x = x + <S as K>::C;
    x
}

#[ensures(result == x)]
pub fn mul_assoc_f32(x: f32) -> f32 {
    let x = x * S::C32;
    x
}
