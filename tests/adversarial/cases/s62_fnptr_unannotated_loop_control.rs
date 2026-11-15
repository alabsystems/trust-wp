//@ expect: verify
//@ mechanism: a UNIQUELY resolvable fn pointer in an unannotated loop whose precondition holds — over-refusal control
//@ accept-means: n/a (control) — `3 > 0` discharges the target's precondition.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x > 0u32)]
#[ensures(result == x)]
pub fn needs_positive(x: u32) -> u32 {
    x
}

#[ensures(result == 7u32)]
pub fn good_fnptr() -> u32 {
    let f: fn(u32) -> u32 = needs_positive;
    let mut i = 0u32;
    while i < 1u32 {
        let _unused = f(3u32);
        i += 1u32;
    }
    7u32
}
