//@ expect: verify
//@ xfail: the loop's exit VC reads `^a` at a pointee that keeps its function-entry value, so it
//@ xfail: cannot state the store `*a = 7` before the loop, and its refutation is withheld.
//@ xfail-verdict: unknown
//@ mechanism: control: `(^a)@ == 7` is TRUE, the loop never touches `*a`. The exit VC read the
//@ mechanism: pointee at its entry value and reported the model as a validated `FAILED (loop
//@ mechanism: invariant)` (`loop_postcondition status=failed`) before D-225, a refutation of a true
//@ mechanism: program.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures((^a)@ == 7)]
pub fn f(a: &mut u32) {
    *a = 7;
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
}
