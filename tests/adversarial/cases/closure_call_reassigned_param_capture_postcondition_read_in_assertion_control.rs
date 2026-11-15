//@ expect: verify
//@ xfail: a `move` closure's `ensures(result@ == x@)` over a capture of a reassigned parameter: the
//@ xfail: call binds the capture by the closure's own name table and states the credit over the
//@ xfail: post-call value of the constant the capture holds (`^Int(5)`), which the final-collapse
//@ xfail: guard's constant-carrier arm refuses (D-14), and the closure's own lane refutes its TRUE
//@ xfail: clause. The campaign driver credited the caller's assertion, beside the same refutation
//@ xfail: of the closure. Retire this directive when a call of a closure that does not mutate its
//@ xfail: state states its credit over the pre-call capture value and the closure's own lane
//@ xfail: proves the clause.
//@ xfail-verdict: failed
//@ mechanism: control for closure_call_reassigned_param_capture_postcondition_credited_at_entry:
//@ mechanism: the assertion reads the value the closure returns.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
pub fn caller(mut x: i32) {
    x = 5;
    let c = #[ensures(result@ == x@)]
    move || -> i32 { x };
    let r = c();
    proof_assert!(r@ == 5);
}
