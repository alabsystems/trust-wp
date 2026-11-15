//@ expect: verify
//@ mechanism: control for s59_ens_stale_param_pointee_reborrow_write without its false ensures:
//@ mechanism: `i@ <= 3` is TRUE and inductive. The loop lane synthesized `*r == 7` from the store
//@ mechanism: through the reborrow, could not state that goal for a reference the body re-binds,
//@ mechanism: and reported the conjecture's failure as a validated `FAILED (loop invariant)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32) -> u32 {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { let r = &mut *a; *r = 7; i += 1; }
    *a
}
