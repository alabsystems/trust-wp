//@ expect: reject
//@ mechanism: the logic-lane spelling of program_ensures_result_param_returned_read_as_ok.rs: a logic function returns its `Result<Int, Int>` parameter unchanged and claims it is `Ok`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) is written for a body MIR unwrapped from its constructor: when a postcondition compares `result` with a constructor, the body is wrapped in one (`encode_branch_as_datatype`), and a body that is already a value of the datatype (an unannotated logic parameter, read as an `Int`) is wrapped too, so `result` is read as `Ok(..)`. Its postcondition is then an axiom every caller reads.
//@ fixed-by: D-165
//@ accept-means: a logic function is credited with a postcondition its body violates, and callers are handed it as a fact; the crate exits 0.
//@ WHY IT IS FALSE: `caller(Err(0))` is `Err(0)`, which the `Err(_) => false` arm matches.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: creusot_test::caller verified ✓`. At D-165: `trust-wp: creusot_test::caller postcondition FAILED (logic postcondition)`.
//@ verdict: error
//@ refused-with: creusot_test::caller postcondition FAILED (logic postcondition)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(match result { Ok(_) => true, Err(_) => false })]
pub fn caller(r: Result<Int, Int>) -> Result<Int, Int> {
    r
}
