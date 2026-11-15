//@ expect: reject
//@ mechanism: Generic Fn-bound call obligation. A contractless function that calls through
//@ mechanism: `F: Fn(u32) -> u32` owes Creusot's `call requires` goal `f.precondition((x,))`.
//@ mechanism: Before discovery covered such functions they were never verification targets,
//@ mechanism: so the goal was silently dropped and the run examined nothing (exit 0).
//@ fixed-by: discover_generic_fn_bound_call_functions (callbacks/discovery/mod.rs)
//@ accept-means: the call-site precondition of a generic closure call is not being checked.
//@ teeth: instantiate with a closure whose precondition is false for 0: `apply_zero(#[requires(x@ > 0)] |x| x)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// No contract: `f`'s precondition at 0 is unknown, so this must NOT verify.
pub fn apply_zero<F: Fn(u32) -> u32>(f: F) -> u32 {
    f(0)
}
