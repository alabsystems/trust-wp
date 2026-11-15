//@ expect: reject
//@ verdict: unknown
//@ mechanism: the other-trait spelling of refinement_blanket_impl_inherent_shadow. The trait clause `assoc.holds()` names `AssocTrait::holds` (its only bound), whose implementation at `AssocStruct` is a BLANKET impl; a DIFFERENT trait `Other` also declares `holds` and implements it directly for `AssocStruct`. D-155's lookup at the impl, blind to the blanket impl, found that one hit and bound the trait clause to `<AssocStruct as Other>::holds`, the impl's clause names the same id through `Other::holds(assoc)`, and the refinement was compared on it.
//@ fixed-by: D-160 (the trait's clause is the blanket `<AssocStruct as AssocTrait>::holds`, rustc's instance of the declaration at the impl; the refinement is checked against it and is not proved)
//@ accept-means: a trait clause read at an impl was bound to another trait's method of the same name, and the refinement was credited on it.
//@ WHY IT IS FALSE: at `Struct`, the trait promises `result ==> <AssocStruct as AssocTrait>::holds(assoc)`, the blanket `holds` is `false`, and `check` returns `true`. Creusot's `refines` goal for `check` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, before D-160: `<Struct as Trait>::check verified ✓` (true) and `<Struct as Trait>::check refinement verified ✓` (false), with the same verdict for its twin refinement_blanket_impl_other_trait_true_control.rs, whose blanket `holds` is `true`: the credit did not depend on the definition the trait clause names.
//@ also-verified: <Struct as Trait>::check
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
        false
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
