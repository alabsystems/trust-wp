//@ expect: verify
//@ xfail-verdict: unknown
//@ xfail: `g` is reported `unknown (refutation withheld: the violated goal is a type parameter's
//@ xfail: invariant ...)`, never FAILED. `id` holds `inv_T(t)` (D-141), so `id(t.clone())` owes the
//@ xfail: opaque `inv_T` of the clone, and no call result is granted `inv_T(result)`: nothing
//@ xfail: discharges it. `inv_T` has no definition, so a model that falsifies it describes no
//@ xfail: instantiation, and the verdict gate withholds that refutation. Creusot's clone carries
//@ xfail: `inv(result)` and verifies `g`; its no-Invariant twin verifies. Retire this directive
//@ xfail: when a call result is granted its type parameter's invariant (and every body returning
//@ xfail: a `T` owes it).
//@ mechanism: a value of a type parameter obtained from a CALL, handed to a generic function with a
//@ mechanism: contract. The price of D-141 charging `inv_T` at every call that fixes `T` while
//@ mechanism: granting it only to parameters. With the verdict gate disabled by a local knob `g` is
//@ mechanism: printed `FAILED` with a counterexample on this TRUE contract, as it was before the
//@ mechanism: gate; `xfail-verdict: unknown` keeps it from printing that again.
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

#[ensures(result == t)]
pub fn id<T>(t: T) -> T {
    t
}

#[ensures(true)]
pub fn g<T: Clone>(t: &T) -> T {
    id(t.clone())
}
