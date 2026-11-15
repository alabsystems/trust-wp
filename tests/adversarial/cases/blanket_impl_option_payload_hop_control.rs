//@ expect: verify
//@ xfail-verdict: unknown
//@ xfail: `<Option<U> as Total>::total` is `unknown (refutation withheld: goal set carries a
//@ xfail: fail-closed `false` ...)`, never FAILED. Its hop `u.total()` enters an undetermined body,
//@ xfail: and the covering check that would charge `inv_U(u)` there compares clauses positionally:
//@ xfail: this very impl is granted a MATCH over its payload, which it cannot read, so the call
//@ xfail: refuses (D-141). Retire this directive when the covering check reads a decomposition.
//@ mechanism: a TRUE blanket impl over `Option<U>` whose body hops to `U`'s impl inside a match
//@ mechanism: arm. The refused grant is a fail-closed `false`, and the arm's path guard wraps it:
//@ mechanism: `(self.discriminant() == 1) ==> false`, refuted by any `Some` value. Measured on the
//@ mechanism: build before the verdict gate read a guarded marker as one: `FAILED` with the
//@ mechanism: counterexample `self = Some(0)`; `xfail-verdict: unknown` keeps it from printing that
//@ mechanism: again.
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

impl<U: Total> Total for Option<U> {
    fn total(self) -> i32 {
        match self {
            Some(u) => u.total(),
            None => 10,
        }
    }
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}
