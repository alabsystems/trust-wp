//@ expect: verify
//@ xfail: the initialization VC binds `*a` to its function-entry value, so it cannot state the
//@ xfail: store `*a = 7` before the loop: a proof of the invariant there is no credit (fail closed),
//@ xfail: and a model of it is no run of the program, so its refutation is withheld (`the loop VC does
//@ xfail: not state a store through a reference before loop entry`). The call-obligation VC assumes
//@ xfail: the invariant beside the entry-state precondition `(*a)@ == 0` and is vacuous.
//@ xfail-verdict: error
//@ mechanism: control: `(*a)@ == 7` is TRUE at loop entry and preserved. The initialization VC read
//@ mechanism: `*a` at its entry value 0 and refuted the invariant with a validated model
//@ mechanism: (`loop_initialization status=failed`); the function's verdict was the call-obligation
//@ mechanism: VC's vacuity, before and after, so this control pins the phase only through its
//@ mechanism: diagnostics. The verdict must never be FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32) {
    *a = 7;
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (*a)@ == 7)]
    while i < 3 { i += 1; }
}
