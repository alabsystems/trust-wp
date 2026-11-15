//@ expect: verify
//@ xfail: D-163 refuses the grant's `assoc.holds()`: the receiver lookup reads `a::AssocTrait::holds`, rustc's type check of the clause
//@ xfail: resolves the blanket `Other::holds`, and a reading rustc does not confirm is refused, not
//@ xfail: replaced by rustc's. Under rustc's reading the contract holds; retire this when the resolver
//@ xfail: takes rustc's answer where the family holds it.
//@ mechanism: the true twin of trait_logic_grant_projection_in_scope_blanket_trait.rs: the blanket `<AssocStruct as Other>::holds`, what Rust selects in the grant and in `uses_grant`, is `true`, so the grant holds at `O` and `uses_grant` follows from it.
//@ teeth: over-refusal control for the reading of a projection receiver in a trait logic grant: a fix that refuses the shape turns it `unknown` and must record the price here as an xfail.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;

    pub trait AssocTrait {
        #[logic]
        fn holds(self) -> bool;
    }
}

pub trait Other {
    #[logic]
    fn holds(self) -> bool;
}

impl<T> Other for T {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub trait Outer {
    type Assoc: a::AssocTrait;

    #[logic]
    #[ensures(result ==> assoc.holds())]
    fn check(self, assoc: Self::Assoc) -> bool;
}

pub struct AssocStruct;
impl a::AssocTrait for AssocStruct {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub struct O;

impl Outer for O {
    type Assoc = AssocStruct;

    #[logic(open)]
    fn check(self, _assoc: AssocStruct) -> bool {
        true
    }
}

#[ensures(o.check(i) ==> i.holds())]
pub fn uses_grant<T: Outer>(o: T, i: T::Assoc) {}
