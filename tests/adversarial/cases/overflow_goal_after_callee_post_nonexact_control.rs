//@ expect: verify
//@ mechanism: the goal of an arithmetic panic site is owed by a region walk
//@ mechanism: (`collect_arithmetic_panic_obligations`), never recorded in the CallEffects whose premises it
//@ mechanism: would have to guard: a callee postcondition assumed LATER on the path is guarded only by the
//@ mechanism: obligations recorded so far in its own lane, so it discharges the earlier goal. `below`
//@ mechanism: diverges for `x >= 100`, so its postcondition is true, but it holds only after the addition.
//@ mechanism: control: the call precedes the addition, so its postcondition holds where the goal is owed.
//@ mechanism: Twin of overflow_goal_discharged_by_later_callee_post_nonexact.rs.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

#[ensures(result@ == x@ + 1)]
pub fn f(x: u32, a: &mut u32) -> u32 {
    *a = 0;
    below(x);
    x + 1
}
