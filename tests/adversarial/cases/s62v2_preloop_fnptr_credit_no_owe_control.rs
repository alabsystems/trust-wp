//@ expect: verify
//@ mechanism: control for s62v2_preloop_fnptr_credit_no_owe — the identical pre-loop fn-pointer shape with NO unchecked user Drop in the callee's instantiation must still verify, so the fix is a narrowing at the drop shape and not a blanket refusal of pre-loop fn pointers
//@ fixed-by: wp-s62 v2 (resolve_obligation_callee)
//@ accept-means: n/a (control)
//@ teeth: n/a (control) — a failure here means resolve_obligation_callee stopped crediting pre-loop fn pointers at all instead of pairing the credit with the obligation.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x > 0u32)]
#[ensures(result == x)]
pub fn id_pos(x: u32) -> u32 {
    x
}

#[requires(y > 0u32)]
#[ensures(true)]
pub fn need_pos(y: u32) {}

#[ensures(true)]
pub fn credit_in_loop(n: u32) {
    let f: fn(u32) -> u32 = id_pos;
    let mut i = 0u32;
    while i < n {
        let r = f(7u32);
        need_pos(r);
        i = i.wrapping_add(1u32);
    }
}
