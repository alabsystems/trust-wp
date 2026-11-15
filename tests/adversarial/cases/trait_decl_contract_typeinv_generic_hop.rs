//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: the trait-declaration free grant reached through a GENERIC hop. `via<T: Total>`
//@ mechanism: holds `inv_T(t)`, the opaque invariant of its type parameter, and discharges the
//@ mechanism: declaration's `Self` clause at `t.total()` with it; the call `via(s)` fixes
//@ mechanism: `T = Sum10` and owes `Sum10`'s invariant of `s` there (D-141).
//@ accept-means: a generic hop launders the invariant premise: `<Sum10 as Total>::total`
//@ accept-means: reasons from `inv(self)` and the call that instantiates the hop pays nothing,
//@ accept-means: so `caller` may hand the hop anything at all.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, returns 2, and claims 10.
//@ teeth: MEASURED on one build with the instantiating call's clause dropped by a local knob:
//@ teeth: `caller` is credited `verified`, exit 0. The direct-call twin
//@ teeth: trait_decl_contract_typeinv_free_grant is the same shape with no hop.
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
    t.total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    via(s)
}
