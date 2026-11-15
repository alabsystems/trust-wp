//@ expect: verify
//@ mechanism: isolating twin of refinement_blanket_impl_other_trait_shadow: the blanket `AssocTrait::holds` is `true`, so the refinement is valid and Creusot proves it. The pair differs only in that body. The trait's clause at the impl is the blanket `<AssocStruct as AssocTrait>::holds` (rustc's instance of the declaration), the impl's `Other::holds(assoc)` is `<AssocStruct as Other>::holds` (the named trait's one implementation at `AssocStruct`), and the refinement is proved on the two definitions' bodies.
//@ teeth: over-refusal control for D-160: MEASURED refused (`unknown`) with the named-trait narrowing knocked out, where the impl's `Other::holds(assoc)` sees the blanket impl beside `Other`'s; before D-160 it verified for the wrong reason, with the same verdict as its false twin.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Marker {}

pub trait AssocTrait {
    #[logic]
    fn holds(self) -> bool;
}

impl<T: Marker> AssocTrait for T {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub trait Other {
    #[logic]
    fn holds(self) -> bool;
}

pub trait Trait {
    type Assoc: AssocTrait;

    #[ensures(result ==> assoc.holds())]
    fn check(&self, assoc: Self::Assoc) -> bool;
}

pub struct AssocStruct;
impl Marker for AssocStruct {}
impl Other for AssocStruct {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub struct Struct;

impl Trait for Struct {
    type Assoc = AssocStruct;

    #[ensures(result ==> Other::holds(assoc))]
    fn check(&self, assoc: AssocStruct) -> bool {
        true
    }
}
