//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_use_alias_in_trait_impl_method, differing in `#[requires(y > 0)]` on the trait method and the impl alone: every argument either admits is inside `needs_pos`'s precondition.
//@ accept-means: n/a (control) — the renamed call is inside the callee's precondition wherever the method may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

pub trait Tr {
    #[logic]
    #[requires(y > 0)]
    fn m(self, y: Int) -> Int;
}

pub struct S;

pub mod imp {
    use creusot_std::prelude::*;
    use crate::needs_pos as np;

    impl crate::Tr for crate::S {
        #[logic(open)]
        #[ensures(true)]
        #[requires(y > 0)]
        fn m(self, y: Int) -> Int {
            np(y)
        }
    }
}
