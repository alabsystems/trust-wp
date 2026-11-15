//@ expect: verify
//@ xfail: the arithmetic walk binds `a`, which a store through it before the loop makes a second
//@ xfail: definition of, to a range-guarded havoc at the loop header, so the loop call-obligation VC
//@ xfail: leaves free the value `*a` holds on every iteration (7) and cannot prove `*a + 1` in range.
//@ xfail: A model of it picks `u32::MAX` and is no run of the program, so the refutation is withheld
//@ xfail: (`the loop VC leaves free a value code before the loop fixed`), never reported `failed`.
//@ xfail-verdict: unknown
//@ mechanism: control: `*a` is 7 on every iteration, so `s = *a + 1` never overflows; the entry
//@ mechanism: precondition `(*a)@ == u32::MAX` speaks of a value the store replaced. It was reported
//@ mechanism: `FAILED (loop call obligations)` with a validated model before D-228, a refutation of a
//@ mechanism: true program.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 4294967295)]
pub fn f(a: &mut u32) -> u32 {
    *a = 7;
    let mut i = 0u32;
    let mut s = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { s = *a + 1; i += 1; }
    s
}
