//@ expect: verify
//@ mechanism: the TRUE twin of callee_typeinv_free_grant_recursive_self_call: the same
//@ mechanism: self-call, forwarding the parameter the body already holds the invariant
//@ mechanism: for instead of a freshly built value that breaks it. It is what says the
//@ mechanism: reject twin rejects for the broken value and not because a self-call can no
//@ mechanism: longer discharge its own invariant obligation.
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

#[ensures(result@ == 10)]
pub fn total(s: Sum10, n: u32) -> i32 {
    if n == 0 {
        s.a + s.b
    } else {
        total(s, 0)
    }
}
