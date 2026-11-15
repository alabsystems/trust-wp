//@ expect: verify
//@ mechanism: control: the HONEST identity contract. `hand_back` really does return the argument borrow untouched, so its own `#[ensures(result == p)]` must keep verifying.
//@ fixed-by: n/a — this is the over-refusal guard for s48_handback_caller_writes / s48_handback_callee_writes.
//@ teeth: control - must keep verifying. Verified on wp-campaign ff8f5aa6 too
//@ teeth: in the campaign adversarial run over the new cases, so a later refusal here is a real over-tightening. It pins that the narrowing only removes the CALL-SITE framing, not the ability to prove a borrow-returning contract.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == p)]
pub fn hand_back(p: &mut u32) -> &mut u32 {
    p
}
