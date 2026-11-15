//@ expect: reject
//@ verdict: failed
//@ mechanism: the same free capture premise reaching the ASSERTION lane
//@ mechanism: (`proof_assert_wiring` extends the assertion's preconditions with the identical
//@ mechanism: capture-invariant vector). Committed beside the postcondition spelling because
//@ mechanism: a fix that only reached one of the two lanes would leave the other live.
//@ mechanism: The shape is Creusot's closures/10_tyinv with the captured value built locally
//@ mechanism: rather than arriving as a parameter its callers already owe.
//@ fixed-by: D-76 — the construction site owes the capture invariants the body is granted.
//@ accept-means: a proof_assert inside a closure may assume the type invariant of any
//@ accept-means: captured value however that value was built.
//@ WHY THE CONTRACT IS FALSE: `x.0` is 7; the assertion says it is 0, and the closure's
//@ WHY THE CONTRACT IS FALSE: `ensures` claims a result of 0 where it returns 7.
//@ teeth: MEASURED as ACCEPTED, exit 0, "1 verified, 0 failed", proof_assert_verified=1.
//@ also-verified: f::{closure#0}
//@ WHY THE DECLARED ASSERTION IS TRUE: the closure body holds `inv(x)` as a premise that `f`
//@ owes where it builds the closure (D-76), and `f` is refuted there; under that premise
//@ `x.0@ == 0` follows. It stands on the footing of the closure's declared credit, and it
//@ fails at run time only because `f` breaks the invariant.
//@ also-verified-assertion: creusot_test::f::{closure#0}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{invariant::*, prelude::*};

pub struct Zero(pub u32, pub u32);

impl Invariant for Zero {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ == 0 }
    }
}

pub fn f() {
    let x = Zero(7, 1);
    let clos = #[ensures(result@ == 0)]
    || {
        proof_assert!(x.0@ == 0);
        (*&x).0
    };
    clos();
}
