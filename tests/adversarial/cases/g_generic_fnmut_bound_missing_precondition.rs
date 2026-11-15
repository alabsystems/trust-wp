//@ expect: reject
//@ mechanism: Generic FnMut-bound call obligation. `f(0)` through `F: FnMut(u32) -> u32` owes
//@ mechanism: Creusot's `call requires` goal `(*f).precondition((0,))` (std spec FN_MUT_CALL_MUT).
//@ fixed-by: discover_generic_fn_bound_call_functions (callbacks/discovery/mod.rs)
//@ accept-means: the call-site precondition of a generic FnMut call is not being checked.
//@ teeth: a counter closure `#[requires(x@ > 0)] |x| { n += x; n }` called at 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// No contract: `f`'s precondition at 0 is unknown, so this must NOT verify.
pub fn apply_mut_zero<F: FnMut(u32) -> u32>(f: &mut F) -> u32 {
    f(0)
}
