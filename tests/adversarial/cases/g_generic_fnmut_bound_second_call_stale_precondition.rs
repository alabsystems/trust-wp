//@ expect: reject
//@ mechanism: Generic FnMut-bound call precondition must be checked in the CALL-SITE state.
//@ mechanism: The first `f(x)` moves `*f` to a state where only `postcondition_mut` is known, so
//@ mechanism: the second call's goal `precondition((x,))` on the post-state is unknown. An encoding
//@ mechanism: that checks every call's precondition against the entry state would accept this.
//@ fixed-by: n/a (guards the FN_MUT_CALL_MUT call-site state)
//@ accept-means: a generic FnMut call's precondition is being checked against a stale state.
//@ teeth: `#[requires(!*used)] |x| { *used = true; x }` — its precondition is false after one call.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires((*f).precondition((x,)))]
pub fn apply_mut_twice<F: FnMut(u32) -> u32>(f: &mut F, x: u32) -> u32 {
    f(x);
    f(x)
}
