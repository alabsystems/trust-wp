//@ expect: verify
//@ mechanism: control: a loop invariant's cast over a parameter is classified like a function
//@ mechanism: clause's (congruence of `thin`).
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p == q)]
pub fn f(p: *const [u8], q: *const [u8]) {
    let mut i = 0u32;
    #[invariant(p as *const u8 == q as *const u8)]
    while i < 3 {
        i += 1;
    }
}
