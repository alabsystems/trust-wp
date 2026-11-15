//@ expect: reject
//@ mechanism: a call through a generic `Fn` bound in an ANNOTATED loop states `precondition_F f args`, which neither lane can state
//@ fixed-by: s62 (wp-s62, shared loop-call-target classification)
//@ accept-means: the caller would be proved without ever owing the closure's own precondition.
//@ verdict: unknown
//@ refused-with: apply_in_annotated_loop unknown (loop call obligations: refutation withheld: goal set carries a fail-closed
//@ teeth: rejected on wp-campaign 04fc8074 too (by the Fn::call spec path, not by an explicit refusal); s62 makes the refusal explicit and shared with the unannotated lane.
//@ teeth: D-141 RE-PIN (not a weakening). The tooth was `apply_in_annotated_loop FAILED`, and
//@ teeth: that FAILED was the loop's call-obligation check refuting the fail-closed `false` this case
//@ teeth: exists to owe, behind the loop's path guard, with the model `i = 0`: a model of the guard,
//@ teeth: which shows only that the call is reached. The marker is still owed, so
//@ teeth: `apply_in_annotated_loop` is still refused and cannot be credited; only the spelling
//@ teeth: changed, and `refused-with:` names this function's own refusal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 7u32)]
pub fn apply_in_annotated_loop<F: Fn(u32) -> u32>(f: F) -> u32 {
    let mut i = 0u32;
    #[invariant(true)]
    while i < 1u32 {
        let _unused = f(0u32);
        i += 1u32;
    }
    7u32
}
