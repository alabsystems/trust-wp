//@ expect: reject
//@ mechanism: Creusot's `Option::unwrap_logic` requires `self != None`, and the encoder reads the call as the `Some` payload selector, total on `None`: nothing owed the precondition, so the ensures lane credited the function. The walk owes `receiver != None` at the call (`logic_fn_verify::callee_preconditions::std_logic_precondition`).
//@ accept-means: a logic function that unwraps a possibly-`None` option is credited `verified`.
//@ WHY IT IS FALSE: at `o == None` the body evaluates `None.unwrap_logic()`; Creusot's `vc_caller` owes `o != None` and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `creusot_test::caller verified ✓`, the call never examined.
//@ fixed-by: D-119
//@ verdict: unknown
//@ refused-with: caller unknown (logic callee precondition not proved)
//@ note: not refuted: the encoder models `Option<Int>` over `Int` with uninterpreted testers, and no
//@ note: validated model of `o == None` comes back; the goal is examined and not proved.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(true)]
pub fn caller(o: Option<Int>) -> Int {
    o.unwrap_logic()
}
