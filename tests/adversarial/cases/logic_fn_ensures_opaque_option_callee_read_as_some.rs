//@ expect: reject
//@ mechanism: a logic body that is a call of an opaque logic function returning `Option<Int>` (declared `#[logic]` in another module, so its body is not visible here), with `ensures(result != None)`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) is written for a body MIR unwrapped from its constructor: when a postcondition compares `result` with an `Option`/`Result` constructor, the body is re-wrapped into a constructor (`encode_branch_as_datatype`), and a body that is already a value of the datatype (an uninterpreted call of sort `Option<Int>`) is wrapped too, so `result` is read as `Some(..)` and the negated goal is refuted with no search (the trace shows `encoding body (datatype wrap)` and a solve of zero variables). With the callee in the same module, a structural refutation shape (which reads the callee's `None`) withholds the solver's proof; that is how logic_fn_body_some_call_renamed.rs, whose renamed call D-136 settles to exactly this shape, is rejected at the head. Found probing sideways from D-136.
//@ fixed-by: D-165
//@ accept-means: a logic function is credited with a postcondition about an opaque callee that nothing establishes and that is false, and the crate exits 0.
//@ WHY IT IS FALSE: `m::nothing(y)` is `None` for every `y`, so `caller(y)` is `None`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: creusot_test::caller verified ✓`. The control is logic_fn_ensures_opaque_option_callee_read_as_some_control.rs, which claims `result == m::nothing(y)` instead and verifies. At D-165: `trust-wp: creusot_test::caller postcondition FAILED (logic postcondition)`.
//@ verdict: error
//@ refused-with: creusot_test::caller postcondition FAILED (logic postcondition)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m {
    use creusot_std::prelude::*;

    #[logic]
    pub fn nothing(x: Int) -> Option<Int> {
        None
    }
}

#[logic]
#[ensures(result != None)]
pub fn caller(y: Int) -> Option<Int> {
    m::nothing(y)
}
