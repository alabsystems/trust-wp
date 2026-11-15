//@ expect: verify
//@ xfail: the price of refusing method_call_box_receiver_other_trait_out_of_scope.rs. `other::Other` is not in scope where `b.holds()` is written, so Rust derefs the box and selects `<S as AssocTrait>::holds` (`true`) and the contract holds; the typed receiver lookup sees a candidate at the box (`<Box<S> as other::Other>::holds`) and one at `S`, cannot tell that `other::Other` is out of scope (only a trait declared in the call's own module is known to be in it), and refuses.
//@ mechanism: the true twin of method_call_box_receiver_other_trait_out_of_scope.rs: the same impls, with the pointee's `holds` returning `true`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait AssocTrait {
    #[logic]
    fn holds(self) -> bool;
}

pub struct S;
impl AssocTrait for S {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub mod other {
    use creusot_std::prelude::*;
    pub trait Other {
        #[logic]
        fn holds(self) -> bool;
    }
    impl Other for Box<super::S> {
        #[logic(open)]
        fn holds(self) -> bool {
            false
        }
    }
}

// `b.holds()` is <S as AssocTrait>::holds, reached through the box, which is true.
#[ensures(b.holds())]
pub fn f(b: Box<S>) {}
