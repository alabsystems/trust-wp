//@ expect: verify
//@ xfail: the receiver `(&a)` has a reference level the contract parser drops, so the call is
//@ xfail: refused (D-201), where Rust reads `<&A as Invariant>::invariant` (true). Before D-201
//@ xfail: the dropped borrow was read as `A::invariant` (false) and the contract refuted. The
//@ xfail: isolating twin of method_call_borrowed_receiver_read_at_pointee_type_granted.rs.
//@ mechanism: control: `(&a).invariant()` is `<&A as Invariant>::invariant`, true, and `f` returns true.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `f FAILED ✗ (postcondition)` with D-199 in force)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A;
impl A {
    #[logic(open)]
    pub fn invariant(self) -> bool {
        pearlite! { false }
    }
}

#[ensures(result == (&a).invariant())]
pub fn f(a: A) -> bool {
    let _ = a;
    true
}
