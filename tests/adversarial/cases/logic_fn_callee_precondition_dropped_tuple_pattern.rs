//@ expect: reject
//@ mechanism: the tuple-pattern spelling of logic_fn_callee_precondition_dropped_wildcard_scrutinee: a tuple pattern matched against a tuple literal binds each component, and the component under `_` was dropped when it read no name, so `match (needs_pos(0), y) { (_, b) => b }` reached the callee-precondition walk as `y`.
//@ accept-means: a closed call under a `_` of a tuple pattern is never owed.
//@ WHY IT IS FALSE: the body evaluates `needs_pos(0)` on every input.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-119's callee-precondition walk and before this parser fix: `creusot_test::caller verified ✓`.
//@ fixed-by: D-119 — a logic body's elaboration drops no subterm that evaluates a call.
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
    pearlite! { match (needs_pos(0), y) { (_, b) => b } }
}
