//@ expect: reject
//@ mechanism: the UNRESOLVED spelling of trait_impl_escape_withdrawal_leaves_trait_callers_credited:
//@ mechanism: `<S as Tr>::m` hands the `&dyn Fn` it is given to `Option::map`, whose precondition
//@ mechanism: no spec states, so the escape join withdraws the impl; the withdrawal must reach the
//@ mechanism: trait join, which then withdraws `generic_caller`, credited on `Tr::m`'s contract.
//@ accept-means: `generic_caller` is reported `verified` although `generic_caller(&S, Some(5))`
//@ accept-means: panics with "index out of bounds" inside the closure `Option::map` calls.
//@ WHY THE CONTRACT IS FALSE: `generic_caller::<S>(&S, Some(5))` runs `[1u32, 2][5]`.
//@ fixed-by: D-122: an implementation the escape join withdraws did not discharge the contract it owes.
//@ teeth: MEASURED on the binary before D-122: `<S as Tr>::m` withdrawn for the trait object it
//@ teeth: hands over, `generic_caller verified ✓`. After it `generic_caller` is withdrawn too.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

pub trait Tr {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>, f: &dyn Fn(usize) -> u32) -> u32;
}

pub struct S;

impl Tr for S {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>, f: &dyn Fn(usize) -> u32) -> u32 {
        let _ = o.map(f);
        1
    }
}

#[ensures(result@ == 1)]
pub fn generic_caller<T: Tr>(t: &T, o: Option<usize>) -> u32 {
    t.m(o, &|j: usize| [1u32, 2][j])
}
