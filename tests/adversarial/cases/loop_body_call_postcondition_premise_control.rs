//@ expect: verify
//@ mechanism: control: `#[invariant(b)]` over `b = go_m()`, where `go_m` ensures `result`, is TRUE
//@ mechanism: and inductive. The loop body walk kept a callee postcondition only in the shape
//@ mechanism: `result == e`, so `b` after the body was a free variable and preservation reported
//@ mechanism: a model with `b' == false` as a validated `FAILED (loop invariant)`: a refutation of
//@ mechanism: a true program, validated against a premise set the postcondition was never in.
//@ mechanism: The body walk now states every postcondition clause at the call's result, and a
//@ mechanism: premise it cannot state withholds the refutation instead.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn go_m() -> bool { true }

#[ensures(result)]
pub fn go_loop(n: u32) -> bool {
    let mut b = go_m();
    let mut i: u32 = 0;
    #[invariant(b)]
    while i < n {
        b = go_m();
        i += 1;
    }
    b
}
