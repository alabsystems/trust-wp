//@ expect: reject
//@ mechanism: a program function returns its `Option<u32>` parameter unchanged and claims `result != None`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) is written for a body MIR unwrapped from its constructor: when a postcondition compares `result` with an `Option`/`Result` constructor, the body is re-wrapped into a constructor (`encode_branch_as_datatype`), and a body that is already a value of the datatype (a parameter of type `Option<u32>`) is wrapped too, so `result` is read as `Some(..)` and the negated goal is refuted with no search (the trace shows `encoding body (datatype wrap)` and a solve of zero variables). The same holds of a `Result` parameter (program_ensures_result_param_returned_read_as_ok.rs), of an `Option` field (program_ensures_option_field_returned_read_as_some.rs) and in the logic lane (logic_fn_ensures_option_param_returned_read_as_some.rs, logic_fn_ensures_opaque_option_callee_read_as_some.rs); a user enum is read correctly. Found probing sideways from D-136, whose logic_fn_body_some_call_renamed.rs is rejected at the head only because a structural refutation shape withholds the solver's proof of this same reading.
//@ fixed-by: D-165
//@ accept-means: a function that returns `None` for some argument is credited with a postcondition saying it never does, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(None)` returns `None`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: prog verified ✓`. The control is program_ensures_option_param_returned_read_as_some_control.rs, which differs in a `requires(o != None)` alone and verifies. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result != None)]
pub fn prog(o: Option<u32>) -> Option<u32> {
    o
}
