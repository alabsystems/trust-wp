//@ expect: verify
//@ mechanism: `b.holds()` on `b: Box<S>`, where `Other` is implemented for `Box<S>` and `AssocTrait` for `S`, both declared in the module the call is written in. Rust's method probe finds `<Box<S> as Other>::holds` at the box itself, before any deref, so that is the callee (`true`). The typed receiver lookup counts a candidate at every level the autoderef reaches; a trait declared in the call's own module is certainly in scope, so the box level's one candidate decides the call.
//@ teeth: over-refusal control for the in-scope rule of the typed receiver lookup: with every trait counted as possibly out of scope, the box level and its pointee both have a candidate and `f` is refused (`unknown`). Its false twin is method_call_box_receiver_trait_in_scope_false.rs.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait AssocTrait {
    #[logic]
    fn holds(self) -> bool;
}

pub trait Other {
    #[logic]
    fn holds(self) -> bool;
}

pub struct S;
impl AssocTrait for S {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

impl Other for Box<S> {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

#[ensures(b.holds())]
pub fn f(b: Box<S>) {}
