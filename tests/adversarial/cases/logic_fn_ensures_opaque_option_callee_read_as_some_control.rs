//@ expect: verify
//@ mechanism: control for logic_fn_ensures_opaque_option_callee_read_as_some, differing in the postcondition alone: `result == m::nothing(y)` names the callee's value without comparing it with a constructor, so no datatype binding re-wraps the body.
//@ accept-means: n/a (control) — the body is the call the postcondition names.
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
#[ensures(result == m::nothing(y))]
pub fn caller(y: Int) -> Option<Int> {
    m::nothing(y)
}
