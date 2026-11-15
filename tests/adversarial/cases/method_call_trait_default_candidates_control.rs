//@ expect: verify
//@ mechanism: where a trait default is the one definition that runs at the receiver, the lookup binds it: at `S` (`impl AssocTrait for S {}`) `s.holds()` is the default, `true`, and `Other`'s `holds` is implemented only for `N`. Where the impl selected at the receiver defines the method, the default is no candidate: at `V` the impl's own `holds` (`true`) is the one definition.
//@ teeth: over-refusal control for counting a trait default as a candidate of the typed receiver lookup: a default counted where the impl selected at the receiver overrides it, or counted without being bound where it is alone, refuses `at_override` or `at_default` (`unknown`). Its false twins are method_call_trait_default_other_trait_out_of_scope.rs and method_call_blanket_default_other_trait_out_of_scope.rs.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait AssocTrait {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub struct S;
impl AssocTrait for S {}

pub struct V;
impl AssocTrait for V {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub struct N;

pub mod other {
    use creusot_std::prelude::*;
    pub trait Other {
        #[logic]
        fn holds(self) -> bool;
    }
    impl Other for super::N {
        #[logic(open)]
        fn holds(self) -> bool {
            false
        }
    }
}

#[ensures(s.holds())]
pub fn at_default(s: S) {}

#[ensures(v.holds())]
pub fn at_override(v: V) {}
