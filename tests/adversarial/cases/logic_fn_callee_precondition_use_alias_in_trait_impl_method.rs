//@ expect: reject
//@ mechanism: the trait-impl spelling of logic_fn_callee_precondition_use_alias_in_inherent_method.rs: a trait impl's logic method, in a module that imports `use crate::needs_pos as np;`, calls `np(y)`, and `needs_pos` requires `x > 0`. With D-120 open the walk owed nothing for the renamed call; with D-136 it owes what rustc resolved the call to.
//@ accept-means: a trait impl's logic method that calls another function outside its precondition, through a renaming import, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0`, `<S as Tr>::m(S, 0)` calls `needs_pos(0)`, which requires `x > 0`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `trust-wp: creusot_test::imp::<impl Tr for S>::m verified ✓`; FAILED (logic callee precondition) with D-136. The control is logic_fn_callee_precondition_use_alias_in_trait_impl_method_control.rs, which differs in the `requires` of the trait method and the impl alone and verifies with D-136.
//@ fixed-by: D-136
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
    fn m(self, y: Int) -> Int;
}

pub struct S;

pub mod imp {
    use creusot_std::prelude::*;
    use crate::needs_pos as np;

    impl crate::Tr for crate::S {
        #[logic(open)]
        #[ensures(true)]
        fn m(self, y: Int) -> Int {
            np(y)
        }
    }
}
