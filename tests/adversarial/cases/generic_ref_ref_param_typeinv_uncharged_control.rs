//@ expect: verify
//@ xfail: `via` is reported `unknown (refutation withheld: ...)`: it holds nothing about `**t`, so
//@ xfail: the goal `inv_T` of the referent its hop owes is refuted with nothing granting it, and
//@ xfail: D-141 withholds a refutation of the opaque `inv_T`. Retire this directive when a
//@ xfail: parameter holds the invariant of a type parameter behind a second reference
//@ xfail: (generic_ref_ref_param_typeinv_uncharged.rs).
//@ xfail-verdict: unknown
//@ mechanism: the TRUE twin of generic_ref_ref_param_typeinv_uncharged.rs, differing in the value
//@ mechanism: alone: `caller` lends `via` the `Sum10` it was handed, whose invariant holds.
//@ mechanism: The build before D-141 rejects it too: the hop into the impl was refused (D-75).
//@ teeth: n/a — over-refusal control.
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
    fn total(&self) -> i32;
}

impl Total for Sum10 {
    fn total(&self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: &&T) -> i32 {
    (**t).total()
}

#[ensures(result@ == 10)]
pub fn caller(s: Sum10) -> i32 {
    let r = &s;
    via(&r)
}
