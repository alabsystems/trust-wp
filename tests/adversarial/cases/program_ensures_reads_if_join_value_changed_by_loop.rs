//@ expect: reject
//@ mechanism: `let mut m = if c { 1u32 } else { 2u32 }`, a loop that sets `m = 7`, then `m` is returned under
//@ mechanism: `ensures(result <= 2u32)`. After the loop `m` names its exit value; the entry value D-243 states
//@ mechanism: is a premise of the code after the loop only for a local nothing changes from the entry on.
//@ accept-means: a function that returns 7 is credited with returning at most 2.
//@ WHY THE CONTRACT IS FALSE: `f(true)` returns 7.
//@ teeth: rejected before and with D-243; it pins the scope of D-243 (e).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result <= 2u32)]
pub fn f(c: bool) -> u32 {
    let mut m = if c { 1u32 } else { 2u32 };
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3 {
        m = 7;
        i += 1;
    }
    m
}
