//@ expect: verify
//@ xfail-verdict: unknown
//@ xfail: `h` is reported `unknown (refutation withheld: the violated goal is a type parameter's
//@ xfail: invariant ...)`, never FAILED. `h` writes no clause, so it holds no `inv_T(t)` premise
//@ xfail: (D-141 gives a contract-free body none, and its callers owe none), while the trait call
//@ xfail: inside it owes `inv_T(t)` because an impl holds `inv(self)`. Creusot grants `h` the
//@ xfail: premise and verifies it. Retire this directive when a contract-free generic body holds
//@ xfail: its parameters' invariants and its callers pay for them.
//@ mechanism: a contract-free generic function calling a trait method on its `T`, a verification
//@ mechanism: target because of the subtraction it performs. With the verdict gate disabled by a
//@ mechanism: local knob `h` is printed `FAILED` with the counterexample `t = 0` on this TRUE
//@ mechanism: program, as it was before the gate; `xfail-verdict: unknown` keeps it from printing
//@ mechanism: that again.
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

pub fn h<T: Total>(t: T) -> i32 {
    t.total() - 1
}
