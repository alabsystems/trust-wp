//@ expect: reject
//@ mechanism: the contract parser's alias elaboration (`formula::elaborate::resolve_aliases`) reads a field of a tuple literal as that component, `(p, 0).0` as `p`, and so drops every other component. In a logic body a dropped component that calls a contracted function takes its precondition with it: the walk that owes callee preconditions (`logic_fn_verify::callee_preconditions`) reads the parsed body, and `(needs_pos(y), 1).1` reached it as `1`. A logic body is now elaborated keeping every call it evaluates (`resolve_aliases_keeping_calls`), as Creusot's vcgen evaluates every component of the tuple.
//@ accept-means: a call written as a component a projection does not select is never owed.
//@ WHY IT IS FALSE: at `y == 0` the body evaluates `needs_pos(0)`, and `needs_pos` requires `x > 0`.
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
    pearlite! { (needs_pos(y), 1).1 }
}
