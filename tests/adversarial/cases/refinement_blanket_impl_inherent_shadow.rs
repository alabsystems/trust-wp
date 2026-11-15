//@ expect: reject
//@ verdict: unknown
//@ mechanism: at `Struct` the trait's clause `assoc.holds()` names `AssocTrait::holds`, the bound of `Self::Assoc`, whose implementation at `AssocStruct` is the BLANKET `impl<T: Marker> AssocTrait for T`; `AssocStruct` also has an inherent `holds`. D-155 read the trait's clause at the impl by looking the method call up on the receiver's type there, and that lookup compared self types: the blanket impl was invisible to it, the one hit left was the inherent method, the impl's clause (where Rust does pick the inherent method) was bound to the same id, and the scope closure admitted both as one definition. With a non-blanket `impl AssocTrait for AssocStruct` the lookup saw two definitions and refused (refinement_inherent_method_shadows_trait_method.rs).
//@ fixed-by: D-160 (the trait's clause is read in the trait's scope and its declaration call instantiated at the impl by rustc's instance resolution, which is the blanket impl; at `AssocStruct` the impl's own `assoc.holds()` has the blanket impl and the inherent method as candidates and is refused, so the refinement is not checked)
//@ accept-means: a trait clause read at an impl was bound to a method the trait clause never names, and the refinement was credited although the impl breaks the trait's promise to generic callers.
//@ WHY IT IS FALSE: at `Struct`, the trait promises `result ==> <AssocStruct as AssocTrait>::holds(assoc)`, and that blanket `holds` is `false`; `check` returns `true`. Creusot's `refines` goal for `check` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, before D-160: `<Struct as Trait>::check verified ✓` (its own contract, true: in the impl `assoc.holds()` is the inherent method) and `<Struct as Trait>::check refinement verified ✓` (false). Before D-155 the scope closure refused every method call, so this refinement was never credited.
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

pub trait Trait {
    type Assoc: AssocTrait;

    #[ensures(result ==> assoc.holds())]
    fn check(&self, assoc: Self::Assoc) -> bool;
}

pub struct AssocStruct;
impl Marker for AssocStruct {}
impl AssocStruct {
    #[logic(open)]
    pub fn holds(self) -> bool {
        true
    }
}

pub struct Struct;

impl Trait for Struct {
    type Assoc = AssocStruct;

    // Here `assoc.holds()` is the inherent AssocStruct::holds (true).
    #[ensures(result ==> assoc.holds())]
    fn check(&self, assoc: AssocStruct) -> bool {
        true
    }
}
