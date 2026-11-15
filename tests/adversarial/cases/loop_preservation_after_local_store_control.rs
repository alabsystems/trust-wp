//@ expect: verify
//@ xfail: the preservation VC reads `k`, which the loop never writes, at its value before the store
//@ xfail: through `r`, under the pre-loop binding `k == 0`, so it cannot state the store and the
//@ xfail: second invariant's antecedent holds there. The refutation is withheld (`the loop VC does not
//@ xfail: state a store through a reference before loop entry`).
//@ xfail-verdict: unknown
//@ mechanism: control: `k` is 5 once the loop starts, so `k == 0u32 ==> i <= 2u32` holds vacuously
//@ mechanism: and both invariants are inductive. Preservation reported a model with `k == 0` and
//@ mechanism: `i == 3` as a validated `FAILED (loop invariant)` before D-225, a refutation of a true
//@ mechanism: program.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let mut k = 0u32;
    let r = &mut k;
    *r = 5;
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    #[invariant(k == 0u32 ==> i <= 2u32)]
    while i < 3 { i += 1; }
}
