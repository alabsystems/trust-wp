//@ expect: reject
//@ mechanism: reject twin of loop_overflow_after_call_result_control: the callee returns `u32::MAX`,
//@ mechanism: so `x + 1` overflows on the first iteration. The loop call-obligation VC leaves `x`
//@ mechanism: free at the header, so the refutation is withheld as the control's is; the case pins
//@ mechanism: that the withholding rejects, never accepts.
//@ accept-means: `f` computes `u32::MAX + 1` on its first iteration, and trust-wp proved every
//@ accept-means: arithmetic operation in range.
//@ verdict: unknown
//@ refused-with: f unknown (loop call obligations: refutation withheld: the loop VC leaves free a value code before the loop fixed
//@ also-verified: most
//@ teeth: not a false-accept gate: refuted `failed` before D-228 and `unknown` since; `most`'s
//@ teeth: contract is true and credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 4294967295)]
pub fn most() -> u32 { 4294967295u32 }

pub fn f() -> u32 {
    let x = most();
    let mut i = 0u32;
    let mut s = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { s = x + 1; i += 1; }
    s
}
