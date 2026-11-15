//@ expect: verify
//@ mechanism: control for closure_call_reassigned_param_capture_reads_entry_value: the closure's
//@ mechanism: precondition states the value the reassignment leaves.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
pub fn caller(mut x: i32) -> i32 {
    x = 5;
    let c = #[requires(x@ == 5)]
    || -> i32 {
        x
    };
    c()
}
