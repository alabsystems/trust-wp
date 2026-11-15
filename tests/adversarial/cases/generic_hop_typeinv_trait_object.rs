//@ expect: reject
//@ verdict: unknown
//@ mechanism: the generic hop instantiated at a TRAIT OBJECT, `T = dyn Total`. The body `via`
//@ mechanism: enters for `t.total()` is the ERASED type's impl, not one written for
//@ mechanism: `dyn Total`, so no clause at `dyn Total` states what that body was granted, and
//@ mechanism: the instantiating call refuses (D-141).
//@ accept-means: an instantiation that names no impl is charged as if it held nothing, while
//@ accept-means: the impl behind the vtable reasons from `inv(self)`.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1 and hands it over as a
//@ WHY THE CONTRACT IS FALSE: `&dyn Total`; the impl returns 2 and `caller` claims 10.
//@ teeth: UNMEASURED for the trait-object arm alone. The arm does fire at `via(d)`, but with
//@ teeth: it answering invariant-free `caller` is still refused by a second fail-closed site on
//@ teeth: this spelling; generic_hop_typeinv_associated_type is where the same refusal carries
//@ teeth: the verdict.
//@ also-verified: via, <Sum10 as Total>::total
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
pub fn via<T: Total + ?Sized>(t: &T) -> i32 {
    t.total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    let d: &dyn Total = &s;
    via(d)
}
