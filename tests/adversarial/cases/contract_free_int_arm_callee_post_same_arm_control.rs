//@ expect: verify
//@ xfail: capped by D-143: the charge is proved (with D-169 it is owed under the arm's edge, as `below`'s
//@ xfail: postcondition is scoped), but it rests on a callee postcondition, a premise that is no entry fact,
//@ xfail: so D-142's proved edge does not leave the cap: `f unknown (partial: panic paths unchecked (panic call))`.
//@ xfail: Retire this when a decision lifts D-143 for premises D-169 scopes.
//@ mechanism: a clause-free body leaves the clause-free cap when every panic arm's edge is proved dead by the
//@ mechanism: verified VC (D-142); the charge for a panic switch inside an integer match arm is owed under the
//@ mechanism: arm's edge, and the arm's premises are scoped by the same edge (D-169, `guard_int_arm_obligations`):
//@ mechanism: here `$call == 0`, the result of `pick(a)`, which reads through the `&mut` parameter `a`.
//@ mechanism: control: `below(x)` and the panic switch are on arm 0, so no execution panics. Twin of
//@ mechanism: contract_free_int_arm_callee_post_other_arm.rs.
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
