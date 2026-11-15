//@ expect: verify
//@ mechanism: control: the loop writes only a local, never the parameter's pointee, so the entry fact about `*a` stays live through it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
#[ensures(result@ == 0)]
pub fn f(a: &mut u32, n: u32) -> u32 {
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n { i += 1; }
    *a
}
