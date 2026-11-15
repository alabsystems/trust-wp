//@ expect: verify
//@ xfail: `f` is printed FAILED with the counterexample `w = Wrapper(Sum10(0, 0), 0)`, a value
//@ xfail: whose `Sum10` breaks its own invariant, so no execution reaches it: the builder states no
//@ xfail: structural invariant for a plain struct, `f` holds nothing about `w.s`, and the hop
//@ xfail: `w.s.total()` owes `inv(w.s)` with nothing granting it. A false refutation on a TRUE
//@ xfail: program, pinned so a change of flavour is seen; the build before D-141 prints the same
//@ xfail: FAILED. Retire this directive when a plain struct's parameter holds its fields'
//@ xfail: invariants (struct_field_typeinv_uncharged.rs).
//@ xfail-verdict: failed
//@ mechanism: the TRUE twin of struct_field_typeinv_uncharged.rs, differing in the value alone:
//@ mechanism: `caller` wraps the `Sum10` it was handed, whose invariant holds, so `f`'s hop into
//@ mechanism: the impl is sound and Creusot, which gives `f` the structural `inv(w) = inv(w.s)`,
//@ mechanism: verifies both.
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

pub struct Wrapper {
    pub s: Sum10,
    pub k: i32,
}

#[ensures(result@ == 10)]
pub fn f(w: Wrapper) -> i32 {
    w.s.total()
}

#[ensures(result@ == 10)]
pub fn caller(s: Sum10) -> i32 {
    f(Wrapper { s, k: 0 })
}
