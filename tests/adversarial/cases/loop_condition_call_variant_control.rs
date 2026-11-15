//@ expect: verify
//@ mechanism: control: the variant `9 - i@` is non-negative only while the loop condition holds, and
//@ mechanism: the condition reads a call whose clause `result ==> k < 10u32` is not an equation. The
//@ mechanism: variant non-negativity VC assumes the condition, so it must carry the clause too.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result ==> k < 10u32)]
pub fn small(k: u32) -> bool { k < 10 }

pub fn go() {
    let mut i = 0u32;
    #[invariant(i@ <= 10)]
    #[variant(9 - i@)]
    while small(i) { i += 1; }
}
