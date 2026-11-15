//@ expect: reject
//@ verdict: unknown
//@ mechanism: the typed receiver lookup (`identity_typed::resolve_family_on_type`) that binds a colliding method name matches only impls whose self type is the receiver type. Where `s.holds()` is written only `AssocTrait` is in scope, so Rust selects `<S as AssocTrait>::holds` from a BLANKET impl the lookup cannot see; the one hit it finds is `<S as other::Other>::holds`, a trait not in scope there, and it binds that. The lookup predates D-155; found probing sideways from D-155's reuse of it at the impl.
//@ accept-means: a method call in a program function's own clause was bound to an impl Rust never selects at that call, and the function was credited on it.
//@ WHY IT IS FALSE: `s.holds()` is the blanket `AssocTrait::holds`, which is `false`, so `f`'s postcondition is `false`. Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `f verified ✓`, before D-160 and with D-160's applicability test read back to a self-type comparison.
//@ fixed-by: D-160 (the blanket impl rustc's selection picks at `S` is a candidate beside `Other`'s impl, and the call is refused)
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

pub struct S;
impl Marker for S {}

pub mod other {
    use creusot_std::prelude::*;
    pub trait Other {
        #[logic]
        fn holds(self) -> bool;
    }
    impl Other for super::S {
        #[logic(open)]
        fn holds(self) -> bool {
            true
        }
    }
}

// WRONG: here `s.holds()` is <S as AssocTrait>::holds, which is false.
#[ensures(s.holds())]
pub fn f(s: S) {}
