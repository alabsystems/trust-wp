//@ expect: verify
//@ mechanism: the isolating twin of trait_logic_method_bodyless_decl_false_ensures_unrelated_fn_granted:
//@ mechanism: `f` claims the 0 it returns, beside the same unsatisfiable, unimplemented trait logic
//@ mechanism: declaration, and verifies.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(false)]
    fn m(self) -> Int;
}

#[ensures(result == 0i32)]
pub fn f() -> i32 {
    0
}
