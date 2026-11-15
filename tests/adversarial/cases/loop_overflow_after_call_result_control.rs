//@ expect: verify
//@ xfail: the arithmetic walk binds a call's result before the loop to a range-guarded havoc at the
//@ xfail: loop header and states none of the callee's postcondition there, so the loop call-obligation
//@ xfail: VC cannot prove `x + 1` in range. A model of it picks `u32::MAX` although `seven` returns
//@ xfail: 7, so the refutation is withheld (`the loop VC leaves free a value code before the loop
//@ xfail: fixed`), never reported `failed`.
//@ xfail-verdict: unknown
//@ mechanism: control: `x` is 7, so `s = x + 1` never overflows. It was reported
//@ mechanism: `FAILED (loop call obligations)` with a validated model before D-228, a refutation of a
//@ mechanism: true program.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 7)]
pub fn seven() -> u32 { 7 }

pub fn f() -> u32 {
    let x = seven();
    let mut i = 0u32;
    let mut s = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { s = x + 1; i += 1; }
    s
}
