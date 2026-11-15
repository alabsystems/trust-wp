//@ expect: reject
//@ mechanism: the wildcard spelling of logic_fn_callee_precondition_dropped_tuple_component. Alias elaboration reads a `match` whose first arm cannot fail as that arm, and a value a `_` pattern binds is dropped when it reads no name: `match needs_pos(0) { _ => y }` reached the callee-precondition walk as `y`. In a logic body such a value is now kept when it evaluates a call.
//@ accept-means: a closed call in the scrutinee of a match whose first arm is `_` is never owed.
//@ WHY IT IS FALSE: the body evaluates `needs_pos(0)` on every input, and `0 > 0` is false.
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
    pearlite! { match needs_pos(0) { _ => y } }
}
