//@ expect: verify
//@ mechanism: the isolating twin of callee_typeinv_free_grant_recursive_self_call: the same
//@ mechanism: self-call with a caller-built argument, differing only in whether the invariant
//@ mechanism: is satisfied. See callee_typeinv_ctor_arg_trait_method_control for why the
//@ mechanism: free-grant case's own control cannot supply this.
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
        total(Sum10 { a: 4, b: 6 }, 0)
    }
}
