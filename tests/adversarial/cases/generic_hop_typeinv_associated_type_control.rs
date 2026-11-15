//@ expect: verify
//@ xfail: `g` is reported `unknown (refutation withheld: ...fail-closed `false`...)`: the call
//@ xfail: `via(x)` fixes `T` at the projection `<S as Source>::Item`, which names no type in `g`,
//@ xfail: so D-141 refuses to state what that call owes. Retire this directive when a
//@ xfail: projection-typed parameter holds, and its instantiating call owes, the invariant
//@ xfail: (generic_hop_typeinv_associated_type.rs).
//@ xfail-verdict: unknown
//@ mechanism: the TRUE twin of generic_hop_typeinv_associated_type.rs, differing in the value
//@ mechanism: alone: `caller` hands `g::<Src>` the `Sum10` it was handed, whose invariant holds.
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
pub fn caller(s: Sum10) -> i32 {
    g::<Src>(s)
}
