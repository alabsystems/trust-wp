//@ expect: reject
//@ mechanism: the logic-lane spelling of program_ensures_option_param_returned_read_as_some.rs: a logic function returns its `Option<Int>` parameter unchanged and claims `result != None`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) is written for a body MIR unwrapped from its constructor: when a postcondition compares `result` with an `Option`/`Result` constructor, the body is re-wrapped into a constructor (`encode_branch_as_datatype`), and a body that is already a value of the datatype (a parameter of type `Option<Int>`) is wrapped too, so `result` is read as `Some(..)` and the negated goal is refuted with no search (the trace shows `encoding body (datatype wrap)` and a solve of zero variables). Its postcondition is then an axiom every caller reads: a program function claiming `caller(None) != None` is verified beside it. Found probing sideways from D-136.
//@ fixed-by: D-165
//@ accept-means: a logic function is credited with a postcondition its body violates, and callers are handed it as a fact; the crate exits 0.
//@ WHY IT IS FALSE: `caller(None)` is `None`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: creusot_test::caller verified ✓`. The same contract with `#[requires(o != None)]` did not verify when measured (timeout). At D-165: `trust-wp: creusot_test::caller postcondition FAILED (logic postcondition)`.
//@ verdict: error
//@ refused-with: creusot_test::caller postcondition FAILED (logic postcondition)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result != None)]
pub fn caller(o: Option<Int>) -> Option<Int> {
    o
}
