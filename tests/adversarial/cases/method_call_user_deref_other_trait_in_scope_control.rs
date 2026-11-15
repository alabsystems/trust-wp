//@ expect: verify
//@ mechanism: control for method_call_user_deref_other_trait_out_of_scope.rs: the same crate with `use other::Other;`, so Rust's method probe selects `<W as other::Other>::holds` (`true`) at `W` itself, before any deref, and `f`'s postcondition holds.
//@ teeth: over-refusal control for the receiver lookup at a type with a `Deref` impl: a fix that refuses every such receiver turns it `unknown` and must record the price here as an xfail.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait AssocTrait {
    #[logic]
    fn holds(self) -> bool;
}

#[derive(Clone, Copy)]
pub struct S;
impl AssocTrait for S {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

pub struct W(pub S);
impl std::ops::Deref for W {
    type Target = S;
    fn deref(&self) -> &S {
        &self.0
    }
}

pub mod other {
    use creusot_std::prelude::*;

    pub trait Other {
        #[logic]
        fn holds(self) -> bool;
    }

    impl Other for super::W {
        #[logic(open)]
        fn holds(self) -> bool {
            true
        }
    }
}

use other::Other;

#[ensures(w.holds())]
pub fn f(w: W) {}
