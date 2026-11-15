//@ expect: reject
//@ mechanism: the nested spelling of program_ensures_option_param_returned_read_as_some.rs: a program function returns its `Option<Option<u32>>` parameter unchanged and claims `result != None`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) is written for a body MIR unwrapped from its constructor: when a postcondition compares `result` with a constructor, the body is wrapped in one (`encode_branch_as_datatype`), and a body that is already a value of the datatype (a parameter of type `Option<Option<u32>>`) is wrapped too, so `result` is read as `Some(..)`.
//@ fixed-by: D-165
//@ accept-means: a function that returns `None` for some argument is credited with a postcondition saying it never does, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(None)` returns `None`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result != None)]
pub fn prog(o: Option<Option<u32>>) -> Option<Option<u32>> {
    o
}
