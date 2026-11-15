//@ expect: reject
//@ mechanism: the nested `Result` spelling of program_ensures_result_param_returned_read_as_ok.rs: a program function returns its `Result<Option<u32>, u32>` parameter unchanged and claims it is `Ok`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) is written for a body MIR unwrapped from its constructor: when a postcondition compares `result` with a constructor, the body is wrapped in one (`encode_branch_as_datatype`), and a body that is already a value of the datatype (a parameter of type `Result<Option<u32>, u32>`) is wrapped too, so `result` is read as `Ok(..)`.
//@ fixed-by: D-165
//@ accept-means: a function that returns `Err` for some argument is credited with a postcondition saying it never does, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(Err(0))` returns `Err(0)`, which the `Err(_) => false` arm matches.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(match result { Ok(_) => true, Err(_) => false })]
pub fn prog(r: Result<Option<u32>, u32>) -> Result<Option<u32>, u32> {
    r
}
