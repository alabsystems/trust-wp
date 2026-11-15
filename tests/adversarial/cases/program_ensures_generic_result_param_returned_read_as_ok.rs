//@ expect: reject
//@ mechanism: the generic `Result` spelling of program_ensures_result_param_returned_read_as_ok.rs: a program function returns its `Result<T, E>` parameter unchanged and claims the result is `Ok`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) re-wraps the body in a constructor whenever a postcondition compares `result` with an `Option`/`Result` constructor (`encode_branch_as_datatype`), and a body that is already a value of the datatype (a parameter of type `Result<T, E>`) is wrapped too, so `result` is read as `Ok(..)`.
//@ fixed-by: D-165
//@ accept-means: a generic function that returns `Err` for some argument is credited with a postcondition saying it never does, and the crate exits 0.
//@ WHY IT IS FALSE: `prog::<u8, u8>(Err(0))` returns `Err(0)`, which the `Err(_) => false` arm matches.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(match result { Ok(_) => true, Err(_) => false })]
pub fn prog<T, E>(r: Result<T, E>) -> Result<T, E> {
    r
}
