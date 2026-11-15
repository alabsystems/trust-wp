//@ expect: reject
//@ mechanism: annotated_loop_prior_write_prophecy_erased seen from an ordinary caller whose
//@ mechanism: own contract names no prophecy. The free final value reaches it through the
//@ mechanism: callee's postcondition.
//@ accept-means: the annotated-loop grant is not confined to `^`-bearing contracts — it
//@ accept-means: proves ordinary value claims about a caller's locals that are simply wrong.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: go() returns 9, not 0.
//@ teeth: OPEN. Measured ACCEPTED, exit 0.
//@ also-verified: go
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    *r = 9;
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        i += 1;
    }
}

#[ensures(result == 0i32)]
pub fn go() -> i32 {
    let mut v = 0i32;
    f(&mut v);
    v
}
