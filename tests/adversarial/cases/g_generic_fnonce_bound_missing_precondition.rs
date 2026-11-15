//@ expect: reject
//@ mechanism: Generic FnOnce-bound call obligation. `f(0)` through `F: FnOnce(u32) -> u32` owes
//@ mechanism: Creusot's `call requires` goal `f.precondition((0,))` (std spec FN_ONCE_CALL_ONCE).
//@ fixed-by: discover_generic_fn_bound_call_functions (callbacks/discovery/mod.rs)
//@ accept-means: the call-site precondition of a generic FnOnce call is not being checked.
//@ teeth: `apply_once_zero(#[requires(x@ > 0)] move |x| x)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// No contract: `f`'s precondition at 0 is unknown, so this must NOT verify.
pub fn apply_once_zero<F: FnOnce(u32) -> u32>(f: F) -> u32 {
    f(0)
}
