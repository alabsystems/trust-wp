//@ expect: verify
//@ mechanism: control: `^a` is the prophecy value at expiry, not the entry pointee; a loop that writes 7 leaves it 7
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
#[ensures((^a)@ == 7)]
pub fn f(a: &mut u32) {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { *a = 7; i += 1; }
    *a = 7;
}
