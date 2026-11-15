//@ expect: verify
//@ xfail: D-163 refuses the grant's `x.holds()`: the receiver lookup reads `Outer::holds`, rustc's type check of the clause
//@ xfail: resolves the blanket `Other::holds`, and a reading rustc does not confirm is refused, not
//@ xfail: replaced by rustc's. Under rustc's reading the contract holds; retire this when the resolver
//@ xfail: takes rustc's answer where the family holds it.
//@ mechanism: the true twin of trait_logic_grant_self_receiver_by_value_blanket_over_ref.rs: the blanket `Other::holds`, what Rust selects in the grant and in `uses_grant`, is `true`, so the grant holds at `O` and `uses_grant`'s postcondition holds at every `T`.
//@ teeth: over-refusal control for the reading of a generic receiver in a trait logic grant: a fix that refuses the shape turns it `unknown` and must record the price here as an xfail.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

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

pub trait Outer: Sized {
    #[logic]
    fn holds(&self) -> bool;

    #[logic]
    #[ensures(result ==> x.holds())]
    fn check(x: Self) -> bool;
}

pub struct O;

impl Outer for O {
    #[logic(open)]
    fn holds(&self) -> bool {
        true
    }

    #[logic(open)]
    fn check(_x: Self) -> bool {
        true
    }
}

#[ensures(T::check(o) ==> o.holds())]
pub fn uses_grant<T: Outer>(o: T) {}
