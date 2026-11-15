//@ expect: verify
//@ xfail: D-163 refuses the trait clause's `x.holds()`: the receiver lookup reads `Trait::holds`, rustc's type check of the clause
//@ xfail: resolves the blanket `Other::holds`, and a reading rustc does not confirm is refused, not
//@ xfail: replaced by rustc's. Under rustc's reading the contract holds; retire this when the resolver
//@ xfail: takes rustc's answer where the family holds it.
//@ mechanism: the true twin of refinement_self_receiver_by_value_blanket_over_ref_trait_method.rs: the blanket `<Struct as Other>::holds`, what Rust selects for the trait clause's `x.holds()`, is `true`, so `check`'s refinement holds.
//@ teeth: over-refusal control for the reading of a `Self` receiver in a trait clause: a fix that refuses the shape turns it `unknown` and must record the price here as an xfail.
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

pub trait Trait: Sized {
    #[logic]
    fn holds(&self) -> bool;

    #[ensures(result ==> x.holds())]
    fn check(x: Self) -> bool;
}

pub struct Struct;

impl Trait for Struct {
    #[logic(open)]
    fn holds(&self) -> bool {
        true
    }

    #[ensures(result)]
    fn check(x: Self) -> bool {
        true
    }
}
