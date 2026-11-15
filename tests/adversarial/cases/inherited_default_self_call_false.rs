//@ expect: reject
//@ mechanism: isolating twin of `inherited_default_self_call_control`: the same inherited `Self::f()` (the default body, 1) against a body that returns 2
//@ accept-means: `Self::f()` at a concrete `Self` that does not override `f` was bound to something other than the default body, or left unconstrained and read as 2
//@ verdict: failed
//@ fn-failed: <() as Foo>::get
//@ teeth: the pair differs only in the returned literal; the control verifies and this is FAILED with a counterexample, so the credit comes from the default's value
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Foo {
    #[logic(open)]
    fn f() -> Int {
        1
    }
    fn get(&self) -> i32;
}

impl Foo for () {
    // WRONG: Self::f() is the default, 1; get() returns 2.
    #[ensures(result@ == Self::f())]
    fn get(&self) -> i32 {
        2
    }
}
