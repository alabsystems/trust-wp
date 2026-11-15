//@ expect: reject
//@ mechanism: reject twin of loop_invariant_entry_after_param_store_control: `(*a)@ == 5` holds of
//@ mechanism: the entry value the initialization VC reads, and not of the `7` the store leaves, so
//@ mechanism: that VC proves a FALSE invariant. Withholding the refutation of the control must keep
//@ mechanism: the fail-closed half: such a proof is no credit.
//@ accept-means: `f` stores 7 before the loop, so `(*a)@ == 5` is FALSE at loop entry, and trust-wp
//@ accept-means: proved it.
//@ teeth: UNVERIFIED as a false-accept gate: rejected `unknown` before and after D-225. It guards the
//@ teeth: fail-closed initialization rule (`invariant_reads_pre_loop_store_at_entry`) that the
//@ teeth: withholding sits beside.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 5)]
pub fn f(a: &mut u32) {
    *a = 7;
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (*a)@ == 5)]
    while i < 3 { i += 1; }
}
