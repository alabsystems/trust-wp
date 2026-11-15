//@ expect: verify
//@ mechanism: the premises one arm walk of a switch records are scoped to that arm by an edge built from
//@ mechanism: a condition that must denote the value the switch tests (`PremiseEdge`). `small(a)` reads
//@ mechanism: through the `&mut` parameter `a`, so the switch is not value-stable; the edge is built from
//@ mechanism: the call's own result symbol, which names the value the switch reads.
//@ mechanism: control: the call and the panic switch are on the same arm, so `below`'s postcondition holds
//@ mechanism: wherever the panic goal is owed. Twin of call_result_switch_premise_on_other_arm.rs. Without a
//@ mechanism: faithful edge the arm's premise is dropped and the panic goal is refuted.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (x@ < 100))]
pub fn small(x: &u32) -> bool {
    *x < 100
}

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

#[ensures(true)]
pub fn f(x: u32, a: &mut u32) {
    if small(a) {
        below(x);
        if x >= 100 {
            panic!()
        }
    }
}
