//@ expect: verify
//@ mechanism: control: `while small(i)`, where `small` ensures `result == (k < 10u32)`. The call
//@ mechanism: runs at every pass through the header, so `i < 10` holds in the body and `i >= 10` at
//@ mechanism: the exit: `i <= 10u32` is TRUE and inductive and the loop returns 10. The condition
//@ mechanism: read the call's destination as a free placeholder, so preservation reported a model
//@ mechanism: with `i == 10` entering the body as a validated `FAILED (loop invariant)`. The loop
//@ mechanism: condition now reads the value the body walk gives the same call.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (k < 10u32))]
pub fn small(k: u32) -> bool { k < 10 }

#[ensures(result == 10u32)]
pub fn go() -> u32 {
    let mut i = 0u32;
    #[invariant(i <= 10u32)]
    while small(i) { i += 1; }
    i
}
