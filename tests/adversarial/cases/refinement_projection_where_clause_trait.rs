//@ expect: reject
//@ mechanism: the trait clause `assoc.holds()` has `assoc: Self::Assoc` with `type Assoc: a::AssocTrait`, and the method's where-clause `Self::Assoc: Other`. `a::AssocTrait` is not in scope where the trait is written; `Other` is, and the where-clause makes it apply, so Rust's method probe selects `<Self::Assoc as Other>::holds`. The refinement reads the trait's clause in the trait's scope (D-160's `ResolveMode::TraitMethodCalls`), where a projection receiver is the declaration of the one trait bounding `Assoc` in its declaration (`identity_typed::decl_for_projection`, which reads `explicit_item_bounds` alone, neither the where-clauses nor which traits are in scope): `a::AssocTrait::holds`. D-156's instantiation then makes it `<AssocStruct as a::AssocTrait>::holds` at the impl, D-155's admission lets the id through the scope closure, and the refinement is checked against the wrong definition.
//@ accept-means: a trait clause read at an impl was bound to a trait Rust does not select at the clause, and the refinement was credited on it.
//@ WHY IT IS FALSE: at `Struct`, the trait promises `result ==> <AssocStruct as Other>::holds(assoc)`, that `holds` is `false`, and `check` returns `true`. Creusot's `refines` goal for `check` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `<Struct as Trait>::check refinement verified ✓`, with the identical verdict for its twin refinement_projection_where_clause_trait_true_control.rs (`<AssocStruct as Other>::holds` is `true`). Built before D-155 the same case is rejected (`unknown`): the scope closure refused every logic-function call in a refinement clause (`trait ensures clause names method call `.holds(..)`, which cannot be resolved in the clause's own scope`). D-155's admission of an instantiated id is what turned the misreading below it into a credit. At D-163: rejected (`unknown`), the refinement refused; its twin is refused the same way (xfail, the price).
//@ fixed-by: D-163. rustc's type check of the trait clause, in the trait method's own environment (the where-clause included), resolves `assoc.holds()` to `Other::holds`, not the lookup's `a::AssocTrait::holds`, so the call is refused and the refinement with it.
//@ also-verified: <Struct as Trait>::check
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

pub trait Trait {
    type Assoc: a::AssocTrait;

    #[ensures(result ==> assoc.holds())]
    fn check(&self, assoc: Self::Assoc) -> bool
    where
        Self::Assoc: Other;
}

pub struct AssocStruct;
impl a::AssocTrait for AssocStruct {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

impl Other for AssocStruct {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

pub struct Struct;

impl Trait for Struct {
    type Assoc = AssocStruct;

    #[ensures(result ==> a::AssocTrait::holds(assoc))]
    fn check(&self, assoc: AssocStruct) -> bool {
        true
    }
}
