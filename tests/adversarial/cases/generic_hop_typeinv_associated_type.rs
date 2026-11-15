//@ expect: reject
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: the type parameter fixed at an ASSOCIATED TYPE. `g<S>(x: S::Item)` hands `x` to
//@ mechanism: `via<T>` at `T = <S as Source>::Item`, a projection that names no type in `g`, so
//@ mechanism: the instantiating call cannot state what the impl behind it was granted and
//@ mechanism: refuses (D-141). What stays OPEN is the step before: Creusot gives `g` the opaque
//@ mechanism: premise `inv(x)` at the projection and charges `caller`, which fixes `S = Src`,
//@ mechanism: `Sum10`'s invariant of `s`; trust-wp states no clause for a projection-typed
//@ mechanism: parameter, so `caller` owes nothing and is credited.
//@ accept-means: a projection-typed instantiation is charged as if it held nothing, and a
//@ accept-means: broken value reaches the impl through an associated type.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl returns 2, and
//@ WHY THE CONTRACT IS FALSE: `caller` claims 10.
//@ teeth: MEASURED with a projection answered as invariant-free by a local knob: `g` and
//@ teeth: `caller` are both credited, exit 0 — a whole-run false accept. With the refusal in
//@ teeth: place `caller` is still credited: committed RED until a projection-typed parameter
//@ teeth: holds, and its instantiating call owes, the invariant.
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

pub trait Source {
    type Item: Total;
}

pub struct Src;

impl Source for Src {
    type Item = Sum10;
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: T) -> i32 {
    t.total()
}

#[ensures(result@ == 10)]
pub fn g<S: Source>(x: S::Item) -> i32 {
    via(x)
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    g::<Src>(s)
}
