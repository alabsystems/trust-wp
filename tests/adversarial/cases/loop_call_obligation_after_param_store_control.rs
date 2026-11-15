//@ expect: verify
//@ xfail: the loop body walk replaces the precondition of a call whose argument reads a pointee after
//@ xfail: a store through it by the fail-closed marker `i < 3 ==> false`, so the call obligation is
//@ xfail: unprovable and its refutation is withheld (the goal set carries a fail-closed `false`).
//@ xfail-verdict: unknown
//@ mechanism: control: `*a` is 7 on every iteration, so `need_seven(*a)` meets its precondition. The
//@ mechanism: loop call-obligation VC held the marker under its path, which no scan for `false` saw,
//@ mechanism: and every model that reaches the call refutes it: `FAILED (loop call obligations)` with
//@ mechanism: a validated model before D-225, a refutation of a true program.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 7)]
pub fn need_seven(x: u32) {}

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32) {
    *a = 7;
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { need_seven(*a); i += 1; }
}
