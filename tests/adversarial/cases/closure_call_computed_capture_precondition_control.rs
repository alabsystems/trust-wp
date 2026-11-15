//@ expect: verify
//@ mechanism: control for closure_call_computed_capture_precondition_violated: the capture holds a
//@ mechanism: value computed from a parameter, and the closure's precondition states it.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@ < 100)]
pub fn caller(a: i32) {
    let y = a + 1;
    (#[requires(y@ == a@ + 1)]
    || {
        proof_assert!(y@ == a@ + 1);
    })();
}
