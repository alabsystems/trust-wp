//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, <&'a Sum10 as Total>::total
//@ mechanism: the type parameter fixed at a SHARED reference to an invariant-bearing type:
//@ mechanism: `via<T>` is called at `T = &Sum10`, and the impl for it is granted the referent's
//@ mechanism: invariant by the parameter-clause builder. The call that fixes `T` owes what
//@ mechanism: `type_param_invariant_at` answers there, and that is now the SAME function the
//@ mechanism: builder states every parameter's premise with (D-141): a shared reference is transparent,
//@ mechanism: so the call owes `inv(r)` of the referent.
//@ mechanism: The covering check reads the same answer, so `via` is credited too.
//@ accept-means: a type argument that wraps an invariant-bearing type in a reference is charged
//@ accept-means: as if it held nothing, and the caller that broke the referent is credited.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl for `&Sum10`
//@ WHY THE CONTRACT IS FALSE: returns 2, and `caller` claims 10.
//@ teeth: MEASURED on one build with the previous `type_param_invariant_at` restored by a
//@ teeth: local knob: `caller` is printed `verified`, `via` unknown. Without it `caller` is
//@ teeth: refuted on `((1@ + 1@) == 10)`, the invariant unfolded at the value it built.
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

impl<'a> Total for &'a Sum10 {
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
    via(&s)
}
