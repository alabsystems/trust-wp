//@ expect: reject
//@ mechanism: the `*_call_then_direct_write_final_stale` family with the borrow held in a
//@ mechanism: STRUCT parameter instead of being the parameter. Everything else is the same
//@ mechanism: shape: a contracted call takes a reborrow of `w.r`, the call-site
//@ mechanism: instantiation pins that parameter's prophecy, and the body's own later write
//@ mechanism: through `w.r` is what actually decides it. The disqualification set seeds its
//@ mechanism: borrow provenance only from parameters whose own type is `&mut`, while the
//@ mechanism: `mut_ref_param_names` it rides beside uses `type_contains_mut_ref`, so a
//@ mechanism: `&mut` one field deep is invisible to it and the credit is never withdrawn.
//@ mechanism: Measured: seeding it is only half. The set is keyed on the PARAMETER, because
//@ mechanism: MIR provenance is, while the credit reaches the formulas on the field's own
//@ mechanism: carrier `w.0` — so the withdrawal named `w` and the premise named `w.0`, and
//@ mechanism: the grant and its withdrawal went on naming different things.
//@ accept-means: wrapping a `&mut` in a one-field struct restores the whole stale-credit
//@ accept-means: family that the bare-parameter, explicit-reborrow and field spellings close.
//@ WHY THE PROGRAM IS WRONG: `set` leaves `*w.r == 1`, then `*w.r = 2` runs; the caller
//@ WHY THE PROGRAM IS WRONG: sees 2 when the borrow expires. The contract claims 1.
//@ fixed-by: D-80
//@ teeth: LIVE: ACCEPTED. Isolated in both directions on the same binary:
//@ teeth: struct_held_mut_ref_call_no_write_control.rs (call, no later write) VERIFIES and
//@ teeth: struct_held_mut_ref_write_only_final_stale.rs (the same false claim with no call)
//@ teeth: is REJECTED, so it is the call's credit plus the missed write, not the struct.
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W<'a> {
    pub r: &'a mut i32,
}

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires(*(w.r) == 0i32)]
#[ensures(^(w.r) == 1i32)]
pub fn f(w: W<'_>) {
    set(&mut *w.r);
    *w.r = 2i32;
}
