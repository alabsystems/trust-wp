//@ expect: verify
//@ xfail: `small` has no contract, so nothing states the value the loop condition reads and the exit
//@ xfail: cannot show `i >= 10`: unprovable, as in Creusot. The verdict must be `unknown (refutation
//@ xfail: withheld: the loop condition reads a value the loop VC does not state ...)`, never FAILED.
//@ mechanism: control: the program is TRUE (`small(k)` is `k < 10`), and a model of the exit VC or of
//@ mechanism: the function-level check that assumed the negated condition picks the call's result
//@ mechanism: freely. Preservation holds without the condition, so only the exit reads it; that
//@ mechanism: refutation, and the function-level one after it, are withheld.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn small(k: u32) -> bool { k < 10 }

#[ensures(result == 10u32)]
pub fn go() -> u32 {
    let mut i = 0u32;
    #[invariant(i <= 10u32)]
    while small(i) {
        if i < 10u32 { i += 1; }
    }
    i
}
