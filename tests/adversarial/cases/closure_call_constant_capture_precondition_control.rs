//@ expect: verify
//@ mechanism: control for closure_call_constant_capture_precondition_violated: the capture holds
//@ mechanism: the value the closure's precondition names.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn caller() {
    let x = 1i32;
    (#[requires(x@ == 1)]
    || {
        proof_assert!(x@ == 1);
    })();
}
