//@ expect: reject
//@ verdict: unknown
//@ mechanism: `b.holds()` on `b: Box<S>`. `other::Other` is implemented for `Box<S>` but is not in scope where the call is written, so Rust's method probe finds nothing at `Box<S>`, `&Box<S>` or `&mut Box<S>`, derefs the box, and selects `<S as AssocTrait>::holds`. The typed receiver lookup (`identity_typed::resolve_family_on_type`) stops peeling the box because a member is defined on a box (`peel_transparent_boxes`), and then asks only the box level: its one hit is `<Box<S> as other::Other>::holds`, and it binds that. The candidates at the levels Rust reaches after the deref are never counted.
//@ accept-means: a method call on a box was bound to a trait not in scope at the box level, where Rust selects the in-scope trait's method on the boxed type, and the function was credited on it.
//@ WHY IT IS FALSE: `b.holds()` is `<S as AssocTrait>::holds`, which is `false`, so `f`'s postcondition is `false`. Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `f verified ✓`, before D-162 and with D-162's deeper levels knocked out (the first level with a candidate answering alone).
//@ fixed-by: D-162 (the box and its pointee both have a candidate, `other::Other` is not declared in the call's module, and the call is refused)
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
        false
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
            true
        }
    }
}

// WRONG: here `b.holds()` is <S as AssocTrait>::holds, reached through the box, which is false.
#[ensures(b.holds())]
pub fn f(b: Box<S>) {}
