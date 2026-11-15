//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: Runner::<T>::run, <Sum10 as Total>::total
//@ mechanism: the type parameter belongs to the IMPL, not the method: `impl<T: Total> Runner<T>`
//@ mechanism: gives `run(&self, t: T)` the premise `inv_T(t)`, and the call on a
//@ mechanism: `Runner<Sum10>` resolves to that body at `T = Sum10` and owes `Sum10`'s invariant
//@ mechanism: of `t` (D-141).
//@ accept-means: an impl's own generics are never instantiated at a call, so a method of a
//@ accept-means: generic impl launders its type-parameter arguments.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl returns 2, and
//@ WHY THE CONTRACT IS FALSE: `caller` claims 10.
//@ teeth: MEASURED with the instantiating call's clause dropped by a local knob: `caller` is
//@ teeth: credited `verified`, exit 0.
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

pub struct Runner<T>(pub i32, pub std::marker::PhantomData<T>);

impl<T: Total> Runner<T> {
    #[ensures(result@ == 10)]
    pub fn run(&self, t: T) -> i32 {
        t.total()
    }
}

#[ensures(result@ == 10)]
pub fn caller(r: Runner<Sum10>, mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    r.run(s)
}
