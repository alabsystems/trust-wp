//@ expect: verify
//@ xfail: D-163 refuses `t.holds()`: the receiver lookup reads `AssocTrait::holds`, rustc's type check of the clause
//@ xfail: resolves the blanket `Other::holds`, and a reading rustc does not confirm is refused, not
//@ xfail: replaced by rustc's. Under rustc's reading the contract holds; retire this when the resolver
//@ xfail: takes rustc's answer where the family holds it.
//@ mechanism: the true twin of method_call_generic_receiver_by_value_blanket_over_ref_bound.rs: the blanket `<T as Other>::holds`, what Rust selects for `t.holds()`, is `true`, so `f`'s postcondition holds.
//@ teeth: over-refusal control for the reading of a generic receiver: a fix that refuses the shape turns it `unknown` and must record the price here as an xfail.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait AssocTrait {
    #[logic]
    #[ensures(result)]
    fn holds(&self) -> bool;
}

pub trait Other {
    #[logic]
    fn holds(self) -> bool;
}

impl<U> Other for U {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub struct S;
impl AssocTrait for S {
    #[logic(open)]
    #[ensures(result)]
    fn holds(&self) -> bool {
        true
    }
}

#[ensures(t.holds())]
pub fn f<T: AssocTrait>(t: T) {}
