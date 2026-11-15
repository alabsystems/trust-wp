//@ expect: reject
//@ mechanism: the `Result` spelling of program_ensures_option_param_returned_read_as_some.rs: a program function returns its `Result<u32, u32>` parameter unchanged and claims it is `Ok`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) is written for a body MIR unwrapped from its constructor: when a postcondition compares `result` with an `Option`/`Result` constructor, the body is re-wrapped into a constructor (`encode_branch_as_datatype`), and a body that is already a value of the datatype (a parameter of type `Result<u32, u32>`) is wrapped too, so `result` is read as `Ok(..)` and the negated goal is refuted with no search (the trace shows `encoding body (datatype wrap)` and a solve of zero variables). Found probing sideways from D-136.
//@ fixed-by: D-165
//@ accept-means: a function that returns `Err` for some argument is credited with a postcondition saying it never does, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(Err(0))` returns `Err(0)`, which the `Err(_) => false` arm matches.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(match result { Ok(_) => true, Err(_) => false })]
pub fn prog(r: Result<u32, u32>) -> Result<u32, u32> {
    r
}
