//@ expect: reject
//@ mechanism: isolating twin of `refinement_assoc_method_call_control`: the impl promises only `result ==> true` while the trait demands `result ==> assoc.holds()`, and at this impl `holds` is `false`; read at the impl's associated type, the trait clause is false for `result = true`
//@ accept-means: the trait clause's method call was read at some other type, or matched against the impl clause as text, and the refinement was credited, so a generic caller of `Trait::check` would be promised `assoc.holds()` from a `true` result
//@ verdict: failed
//@ also-verified: <Struct as Trait>::check
//@ teeth: the pair differs only in the impl's ensures and `holds`'s body; the control's refinement verifies and this one is FAILED (`check`'s own contract, `result ==> true`, is true and declared)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait AssocTrait {
    #[logic]
    fn holds(self) -> bool;
}

pub trait Trait {
    type Assoc: AssocTrait;

    #[ensures(result ==> assoc.holds())]
    fn check(&self, assoc: Self::Assoc) -> bool;
}

pub struct AssocStruct;
pub struct Struct;

impl AssocTrait for AssocStruct {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

impl Trait for Struct {
    type Assoc = AssocStruct;

    // WRONG refinement: check returns true, and holds() is false here.
    #[ensures(result ==> true)]
    fn check(&self, assoc: AssocStruct) -> bool {
        true
    }
}
