//@ expect: verify
//@ xfail: OPEN false refutation. Neither function returns, so no return state exists and
//@ xfail: `ensures(false)` holds (partial correctness, as i3_never_fn_loop_control reads a `-> !` spin).
//@ xfail: `stop` reaches the function-level check with no extracted body and `stop_inv` is deferred
//@ xfail: there by the loop lane; each is reported `FAILED` with a validated counterexample (`k = 0`)
//@ xfail: to a VC that states no path to a return.
//@ mechanism: control: a body that never returns, unannotated (`loop {}`) and annotated
//@ mechanism: (`#[invariant(true)] loop {}`). A model of a postcondition VC is a counterexample only
//@ mechanism: at a state some path reaches the return with.
//@ teeth: n/a — control. Refuted `FAILED` before D-219 and since.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(false)]
pub fn stop(k: u32) -> bool { loop {} }

#[ensures(false)]
pub fn stop_inv(k: u32) -> bool {
    #[invariant(true)]
    loop {}
}
