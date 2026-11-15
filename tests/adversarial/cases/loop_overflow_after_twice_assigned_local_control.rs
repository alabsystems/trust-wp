//@ expect: verify
//@ xfail: `k` has two definitions before the loop, so the arithmetic walk binds it to a
//@ xfail: range-guarded havoc at the loop header and the loop call-obligation VC cannot prove `k + 1`
//@ xfail: in range. A model of it picks `u32::MAX` although `k` is `n < 10` on every iteration, so
//@ xfail: the refutation is withheld (`the loop VC leaves free a value code before the loop fixed`),
//@ xfail: never reported `failed`.
//@ xfail-verdict: unknown
//@ mechanism: control: the second assignment leaves `k == n`, below 10, so `s = k + 1` never
//@ mechanism: overflows. It was reported `FAILED (loop call obligations)` with a validated model
//@ mechanism: before D-228, a refutation of a true program.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ < 10)]
pub fn f(n: u32) -> u32 {
    let mut k = 4294967295u32;
    k = n;
    let mut i = 0u32;
    let mut s = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { s = k + 1; i += 1; }
    s
}
