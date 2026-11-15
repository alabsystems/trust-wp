//@ expect: verify
//@ mechanism: the refinement of a trait method whose clause calls a method on an associated-type parameter (should_succeed/bug/464's shape): the trait's `assoc.holds()` read at `impl Trait for Struct` is `<AssocStruct as AssocTrait>::holds`, the impl's call names the same definition, and the refinement holds
//@ teeth: over-refusal control — measured `trait refinement error: trait ensures clause names method call `.holds(..)`` before method calls were resolved on each side's receiver types; `<Struct as Trait>::check refinement verified ✓`, exit 0, after
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
        true
    }
}

impl Trait for Struct {
    type Assoc = AssocStruct;

    #[ensures(result ==> assoc.holds())]
    fn check(&self, assoc: AssocStruct) -> bool {
        true
    }
}
