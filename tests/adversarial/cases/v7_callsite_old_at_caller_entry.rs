//@ expect: reject
//@ mechanism: a callee's `old(e)` is `e` in the callee's entry state, which is the CALL's
//@ mechanism: pre-state. The call substituted the arguments under `old(..)` and left it, so the
//@ mechanism: caller read it in the CALLER's entry state: after `*x = 5`, `get(x)`'s
//@ mechanism: `result == old(*p)` told the caller `result == *x` of its own entry `*x`.
//@ accept-means: a value a callee reads at its entry is the caller's entry value, whatever the
//@ accept-means: caller wrote before the call.
//@ WHY THE CONTRACT IS FALSE: the result is 5, and the entry `*x` is arbitrary.
//@ fixed-by: D-101 (at a call, `old(e)` is `e` read where the arguments are; an argument whose
//@ fixed-by: translation reads a pointee's entry value after a store gives no reading there)
//@ teeth: MEASURED on d73d0571 (debug driver): `get_caller_false verified`. On the D-101 tree:
//@ teeth: unknown.
//@ also-verified: get
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == old(*p))]
pub fn get(p: &mut i32) -> i32 {
    *p
}

#[ensures(result == *x)]
pub fn get_caller_false(x: &mut i32) -> i32 {
    *x = 5;
    get(x)
}
