//@ expect: reject
//@ mechanism: an indirect call through a REASSIGNED local in an unannotated loop has no unique target
//@ fixed-by: s62 (wp-s62, shared loop-call-target classification)
//@ accept-means: a call whose target depends on a runtime branch owed neither target's precondition.
//@ verdict: unknown
//@ refused-with: evil_reassigned unknown (refutation withheld: goal set carries a fail-closed
//@ teeth: verified ✓ (exit 0) on wp-campaign 04fc8074 (debug driver); FAILED ✗ on wp-s62 — a second live false accept of the same defect.
//@ also-verified: needs_positive
//@ teeth: D-141 RE-PIN (not a weakening). The tooth was `evil_reassigned FAILED`, and that FAILED was a
//@ teeth: model of the path guard around the fail-closed `false` this case exists to owe:
//@ teeth: the violated goal was `g ==> false`, which every model of `g` refutes, so it showed
//@ teeth: only that the refused construct is reached.
//@ teeth: Its model was `c = false`, the path on which `f` is `other`, which has no precondition
//@ teeth: to violate. The twin s62_fnptr_reassigned_unannotated_loop_value_control, whose contract
//@ teeth: is TRUE, printed `evil_reassigned FAILED` with the same model on the build that read only
//@ teeth: a bare `false` as a marker, and the same `unknown` as this case on the build that reads a
//@ teeth: guarded one.
//@ teeth: The marker is still owed, so `evil_reassigned` is still refused and cannot be credited; only
//@ teeth: the spelling changed, and `refused-with:` names this function's own refusal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x > 0u32)]
#[ensures(result == x)]
pub fn needs_positive(x: u32) -> u32 {
    x
}

pub fn other(x: u32) -> u32 {
    x
}

#[ensures(result == 7u32)]
pub fn evil_reassigned(c: bool) -> u32 {
    let mut f: fn(u32) -> u32 = other;
    if c {
        f = needs_positive;
    }
    let mut i = 0u32;
    while i < 1u32 {
        let _unused = f(0u32);
        i += 1u32;
    }
    7u32
}
