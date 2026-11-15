//@ expect: verify
//@ xfail: FAILED on a TRUE program. `hop` runs a local closure that hands `take` a valid `Sum10`; the
//@ xfail: call `c()` owes the closure's precondition, its body's WP (D-54), which carries `take`'s
//@ xfail: grant as `inv` of the aggregate the closure builds
//@ xfail: (`__trust_wp_tuple2(3, 7).__trust_wp_invariant_..._Sum10()`). The D-65 unfold does not read
//@ xfail: an aggregate that reaches the caller through a closure's WP, so the invariant stays
//@ xfail: uninterpreted and a model refutes it. Open; found probing D-141's routes sideways.
//@ xfail-verdict: failed
//@ mechanism: a contract-free caller that reaches a granted body through a local closure. The route
//@ mechanism: is charged (the closure's WP carries the grant); the value it hands in keeps its
//@ mechanism: invariant, so the program is TRUE, and a fix of the unfold must verify it.
//@ teeth: control — the same FAILED on this build with the three route arms knobbed off: the
//@ teeth: defect is the unfold's, not the discovery's.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Sum10 {
    pub a: i32,
    pub b: i32,
}

impl Invariant for Sum10 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

#[ensures(result@ == 10)]
pub fn take(t: Sum10) -> i32 {
    let r = t.a + t.b;
    100 / (r - 2) + 10 - 100 / (r - 2)
}

pub fn hop() -> i32 {
    let c = || take(Sum10 { a: 3, b: 7 });
    c()
}
