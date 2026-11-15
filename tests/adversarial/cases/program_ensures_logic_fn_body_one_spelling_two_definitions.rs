//@ expect: reject
//@ mechanism: the defining-axiom spelling of logic_fn_body_one_spelling_two_definitions: the contract-free `same` reads its two `k(y)` calls as one uninterpreted function although rustc resolves them to `zero` and `one`, and a program function's `ensures` unfolded that definition. The misread body is hidden (D-136), and `prog` is refuted. Found probing sideways from the resolution record.
//@ accept-means: a program function is credited on `same(x@)`, which is `zero(x@) == one(x@)`, false, and the crate exits 0.
//@ WHY IT IS FALSE: `same(y)` is `0 == 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `prog verified ✓`. The control is program_ensures_logic_fn_body_one_spelling_two_definitions_control.rs.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn zero(x: Int) -> Int {
    0
}

#[logic]
pub fn one(x: Int) -> Int {
    1
}

use crate::one as k;

#[logic(open)]
pub fn same(y: Int) -> bool {
    let a = {
        use crate::zero as k;
        k(y)
    };
    a == k(y)
}

#[ensures(same(x@))]
pub fn prog(x: u32) {}
