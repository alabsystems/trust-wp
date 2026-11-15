//@ expect: reject
//@ mechanism: a LOCAL contract-less callee that mutates through `&mut` must not be modelled as effect-free
//@ accept-means: the caller proved a postcondition the callee's mutation falsifies — the `&mut` havoc was lost when the fail-closed `requires(false)` came off the local opaque call
//@ fixed-by: n/a — this is the s80 FALSE-ACCEPT gate, not a defect fix
//@ teeth: rejected on wp-s80 base (the `requires(false)` fires) AND after the s80 fix (route (a) leaves this call Opaque). Prospective for routes (b)/(c): if the `Bool(false)` is dropped for local callees, this case is accepted unless `propagate_mutating_ref_arg_states` really havocs `v`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// Contract-less, LOCAL, and it writes through its `&mut` argument.
fn bump(x: &mut u32) {
    *x += 1;
}

// WRONG: caller(1) returns 2, not 1.
#[requires(a@ < 100u32@)]
#[ensures(result@ == a@)]
pub fn caller(a: u32) -> u32 {
    let mut v = a;
    bump(&mut v);
    v
}
