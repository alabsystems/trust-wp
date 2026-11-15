//@ expect: verify
//@ mechanism: control for callee_post_on_other_arm_flows_out_through_ite.rs: the claim is made only where
//@ mechanism: the arm that establishes it ran, so the premise scoped to that arm's edge proves it.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100 && result == x)]
pub fn below(x: u32) -> u32 {
    #[invariant(true)]
    while x >= 100 {}
    x
}

#[ensures(flag ==> result@ < 100)]
pub fn f(x: u32, flag: bool) -> u32 {
    if flag { below(x) } else { x }
}
