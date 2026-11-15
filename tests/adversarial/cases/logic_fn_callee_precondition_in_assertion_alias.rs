//@ expect: reject
//@ mechanism: the assertion spelling of logic_fn_callee_precondition_use_alias: the renamed call sits inside a `proof_assert!` of the logic body, `proof_assert!(np(y) == np(y))`. The assertion is true of any function, so D-106's assertion lane proves it, and the callee-precondition walk (which reads a call's SPELLING, D-120) owes nothing for `np`. Found probing sideways from D-120.
//@ accept-means: a logic function whose assertion calls another outside its precondition is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` the assertion evaluates `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid. The assertion itself holds at every `y` and its credit is TRUE.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `proof_assert in creusot_test::caller verified ✓` and `creusot_test::caller verified ✓`.
//@ fixed-by: D-136
//@ also-verified-assertion: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use crate::needs_pos as np;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    proof_assert!(np(y) == np(y));
    0
}
