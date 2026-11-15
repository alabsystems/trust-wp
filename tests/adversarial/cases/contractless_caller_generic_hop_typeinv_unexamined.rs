//@ expect: reject
//@ fn-failed: hop
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: D-141 grants `via<T>` the premise `inv_T(t)` and makes a call that fixes `T` owe it
//@ mechanism: there, but only a verification target has a call lane, and a CONTRACT-FREE caller was
//@ mechanism: one for a local callee's WRITTEN `#[requires]` alone. `hop` hands `via::<Sum10>` a value
//@ mechanism: whose invariant is broken; it is a target because the body its call enters holds a
//@ mechanism: parameter premise (`call_may_enter_invariant_grant`, read by discovery, the extraction
//@ mechanism: gate and the escape join through `fn_owes_abort_or_callee_precondition`), so it owes
//@ mechanism: `inv(Sum10 { a: 1, b: 1 })` at the call and is refuted. The concrete-callee spelling is
//@ mechanism: contractless_caller_concrete_param_typeinv_unexamined.rs.
//@ accept-means: a crate reported verified panics inside a function it credits as panic-free,
//@ accept-means: because the one call that broke the callee's invariant premise is examined by nothing.
//@ WHY THE PROGRAM IS WRONG: `hop()` hands `via` a `Sum10` with `a + b == 2`, the impl returns 2,
//@ WHY THE PROGRAM IS WRONG: and `100 / (r - 2)` in `via` divides by zero.
//@ fixed-by: D-141 — a contract-free body that calls a local body granted a parameter invariant is a
//@ fixed-by: verification target, decided from the vector the spec table stores (`param_invariant_grant`).
//@ teeth: MEASURED on one build with discovery's grant arm knobbed off: ACCEPTED, exit 0; with it,
//@ teeth: `hop` FAILED. REJECTED on the build before D-141 too (`via` refused at its hop, D-75).
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
pub fn via<T: Total>(t: T) -> i32 {
    let r = t.total();
    100 / (r - 2) + 10 - 100 / (r - 2)
}

pub fn hop() -> i32 {
    via(Sum10 { a: 1, b: 1 })
}
