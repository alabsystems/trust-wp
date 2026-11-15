//@ expect: reject
//@ mechanism: a logic body calls a standard-library PROGRAM method with a precondition, `o.unwrap()` on an `Option<Int>`. The callee-precondition walk refuses a call that may denote one of the CRATE's program functions with a precondition (D-119) and states the preconditions of the standard LOGIC functions it lists; a standard program function is neither, and the encoder reads `unwrap` as the `Some` payload selector, total on `None`. Found probing sideways from D-120.
//@ accept-means: a logic function that calls `Option::unwrap` on a possibly-`None` option is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `o == None` the body evaluates `None.unwrap()`, and `Option::unwrap` requires `self != None` (trust-wp's own standard table states it); Creusot admits no program function in a logic body at all.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The path-call spelling is logic_fn_std_program_method_ufcs_precondition.rs.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(true)]
pub fn caller(o: Option<Int>) -> Int {
    o.unwrap()
}
