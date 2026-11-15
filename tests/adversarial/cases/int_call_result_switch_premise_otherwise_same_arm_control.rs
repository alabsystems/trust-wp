//@ expect: verify
//@ mechanism: an integer match arm's premises and its in-arm obligations are scoped by one edge
//@ mechanism: (`PremiseEdge`, `guard_int_arm_obligations`): here the otherwise arm's `!($call == 0)`.
//@ mechanism: control: `below(x)` and the panic switch are on the otherwise arm. Twin of
//@ mechanism: int_call_result_switch_premise_otherwise_arm.rs.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@ % 3)]
pub fn pick(x: &u32) -> u32 {
    *x % 3
}

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

#[ensures(true)]
pub fn f(x: u32, a: &mut u32) {
    match pick(a) {
        0 => {}
        _ => {
            below(x);
            if x >= 100 {
                panic!()
            }
        }
    }
}
