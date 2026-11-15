//@ expect: reject
//@ mechanism: Creusot's `vc_` for a contracted logic function is `requires ==> wp(body)`, and the wp of a logic call conjoins the callee's `requires` (`backend/logic/vcgen.rs`, `TermKind::Call`: `contract.requires_conj(..).log_and(variant).log_and(ensures ==> k(call))`). trust-wp's logic lane proves `ensures` from the body's value (`verify_logic_fn_postconditions`) and no lane examines the precondition of a logic call inside a logic body, so the function is credited on its `ensures` alone. Pre-existing: the ensures lane is unchanged by D-106; found probing sideways from D-106's logic-body assertion goal.
//@ accept-means: a logic function that calls another outside its precondition is credited `verified`, and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-106 and on the commit before it: `creusot_test::caller verified ✓`.
//@ fixed-by: D-119 — the logic lane owes each call's written `requires` at the call, under the caller's own premises and the path to the call (`logic_fn_verify::callee_preconditions`).
//@ fn-failed: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    needs_pos(y)
}
