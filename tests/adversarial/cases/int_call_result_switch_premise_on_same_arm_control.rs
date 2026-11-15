//@ expect: verify
//@ mechanism: an integer match arm's premises and its in-arm obligations are scoped by one edge
//@ mechanism: (`PremiseEdge`, `guard_int_arm_obligations`): here the call-result edge `$call == 0`, since
//@ mechanism: `pick(a)` reads through the `&mut` parameter `a`.
//@ mechanism: control: `below(x)` and the panic switch are on arm 0, so the postcondition holds wherever the
//@ mechanism: panic goal is owed. Twin of int_call_result_switch_premise_on_other_arm.rs. With the premise
//@ mechanism: scoped and the obligation unconditional, the goal is refuted.
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
        0 => {
            below(x);
            if x >= 100 {
                panic!()
            }
        }
        _ => {}
    }
}
