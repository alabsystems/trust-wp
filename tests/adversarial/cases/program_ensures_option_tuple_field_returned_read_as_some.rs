//@ expect: reject
//@ mechanism: the tuple-field spelling of program_ensures_option_field_returned_read_as_some.rs: a program function returns the `Option<u32>` field `t.1` of its tuple parameter and claims `result != None`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) is written for a body MIR unwrapped from its constructor: when a postcondition compares `result` with a constructor, the body is wrapped in one (`encode_branch_as_datatype`), and a body that is already a value of the datatype (a tuple field of type `Option<u32>`) is wrapped too, so `result` is read as `Some(..)`.
//@ fixed-by: D-165
//@ accept-means: a function that returns `None` for some argument is credited with a postcondition saying it never does, and the crate exits 0.
//@ WHY IT IS FALSE: `prog((0, None))` returns `None`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog unknown (demoted: counterexample verdict withheld — encoding neutralized assumption-position equalities: premise_neutralized_eq(1))`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result != None)]
pub fn prog(t: (u32, Option<u32>)) -> Option<u32> {
    t.1
}
