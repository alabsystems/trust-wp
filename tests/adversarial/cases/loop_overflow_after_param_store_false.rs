//@ expect: reject
//@ mechanism: reject twin of loop_overflow_after_param_store_control: the store before the loop
//@ mechanism: writes `u32::MAX` instead of 7, so `*a + 1` overflows on the first iteration. The loop
//@ mechanism: call-obligation VC leaves `*a` free at the header, so its refutation is withheld as the
//@ mechanism: control's is; the case pins that the withholding rejects, never accepts.
//@ accept-means: `f` computes `u32::MAX + 1` on its first iteration, and trust-wp proved every
//@ accept-means: arithmetic operation in range.
//@ verdict: unknown
//@ refused-with: f unknown (loop call obligations: refutation withheld: the loop VC leaves free a value code before the loop fixed
//@ teeth: not a false-accept gate: refuted `failed` before D-228 and `unknown` since; it pins
//@ teeth: that the refutation D-228 withholds is still a rejection.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32) -> u32 {
    *a = 4294967295u32;
    let mut i = 0u32;
    let mut s = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { s = *a + 1; i += 1; }
    s
}
