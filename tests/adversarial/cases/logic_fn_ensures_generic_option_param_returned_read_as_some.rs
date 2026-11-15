//@ expect: reject
//@ mechanism: the logic-lane spelling of program_ensures_option_param_returned_read_as_some.rs over `Option<T>`: a logic function returns its parameter unchanged and claims `result != None`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) re-wraps the body in a constructor whenever a postcondition compares `result` with an `Option`/`Result` constructor (`encode_branch_as_datatype`), and a body that is already a value of the datatype (a parameter of type `Option<T>`) is wrapped too, so `result` is read as `Some(..)`, and the postcondition is an axiom every caller reads.
//@ fixed-by: D-165
//@ accept-means: a logic function is credited with a postcondition its body violates, and callers are handed it as a fact; the crate exits 0.
//@ WHY IT IS FALSE: `caller::<Int>(None)` is `None`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: creusot_test::caller verified ✓`. At D-165: `trust-wp: creusot_test::caller postcondition FAILED (logic postcondition)`.
//@ verdict: error
//@ refused-with: creusot_test::caller postcondition FAILED (logic postcondition)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result != None)]
pub fn caller<T>(o: Option<T>) -> Option<T> {
    o
}
