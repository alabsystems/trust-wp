//@ expect: reject
//@ mechanism: the where-clause-free spelling of refinement_projection_where_clause_trait.rs. The trait clause `assoc.holds()` has `assoc: Self::Assoc` with `type Assoc: a::AssocTrait`, `a::AssocTrait` is not in scope where the trait is written, and `Other`, in scope, has a blanket `impl<T> Other for T`, so Rust's method probe selects `<Self::Assoc as Other>::holds`. `identity_typed::decl_for_projection` reads only `Assoc`'s declared bound and answers `a::AssocTrait::holds`; D-156's instantiation makes it `<AssocStruct as a::AssocTrait>::holds` at the impl and the refinement is credited against it.
//@ accept-means: a trait clause read at an impl was bound to a trait Rust does not select at the clause, and the refinement was credited on it.
//@ WHY IT IS FALSE: at `Struct`, the trait promises `result ==> <AssocStruct as Other>::holds(assoc)`, the blanket `holds` is `false`, and `check` returns `true`. Creusot's `refines` goal for `check` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `<Struct as Trait>::check refinement verified ✓`, with the identical verdict for its twin refinement_projection_in_scope_blanket_trait_true_control.rs (blanket `holds` is `true`). Built before D-155 the same case is rejected (`unknown`): the scope closure refused every logic-function call in a refinement clause (`trait ensures clause names method call `.holds(..)`, which cannot be resolved in the clause's own scope`). D-155's admission of an instantiated id is what turned the misreading below it into a credit. At D-163: rejected (`unknown`) with that refusal; its twin is refused the same way (xfail, the price).
//@ fixed-by: D-163. rustc's type check of the trait clause resolves `assoc.holds()` to `Other::holds`, not the lookup's `a::AssocTrait::holds`, so the call is refused and the refinement with it (`trait ensures clause names call `__lfidU__holds_N<site>_(..)`, which cannot be resolved in the clause's own scope`).
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

impl<T> Other for T {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

pub trait Trait {
    type Assoc: a::AssocTrait;

    #[ensures(result ==> assoc.holds())]
    fn check(&self, assoc: Self::Assoc) -> bool;
}

pub struct AssocStruct;
impl a::AssocTrait for AssocStruct {
    #[logic(open)]
    fn holds(self) -> bool {
        true
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
