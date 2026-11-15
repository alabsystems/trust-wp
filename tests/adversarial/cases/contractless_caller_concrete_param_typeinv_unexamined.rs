//@ expect: reject
//@ fn-failed: hop
//@ also-verified: take, <Sum10 as Total>::total
//@ mechanism: the concrete-callee spelling of contractless_caller_generic_hop_typeinv_unexamined.rs.
//@ mechanism: `take(t: Sum10)` is granted `inv(t)` by the parameter-clause builder and every call the
//@ mechanism: spec table reaches owes it; a CONTRACT-FREE caller of it is a verification target
//@ mechanism: because the body its call enters holds that premise (`call_may_enter_invariant_grant`),
//@ mechanism: so `hop`, which breaks the invariant, owes it at the call and is refuted.
//@ accept-means: a crate reported verified panics inside a function it credits as panic-free.
//@ WHY THE PROGRAM IS WRONG: `hop()` hands `take` a `Sum10` with `a + b == 2`, the impl returns 2,
//@ WHY THE PROGRAM IS WRONG: and `100 / (r - 2)` in `take` divides by zero.
//@ fixed-by: D-141 — the discovery that makes its generic sibling's caller a target.
//@ teeth: MEASURED on one build with discovery's grant arm knobbed off: ACCEPTED, exit 0; with it,
//@ teeth: `hop` FAILED. ACCEPTED on the build before D-141 as well: older than the type-parameter grant.
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

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(self) -> i32;
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn take(t: Sum10) -> i32 {
    let r = t.total();
    100 / (r - 2) + 10 - 100 / (r - 2)
}

pub fn hop() -> i32 {
    take(Sum10 { a: 1, b: 1 })
}
