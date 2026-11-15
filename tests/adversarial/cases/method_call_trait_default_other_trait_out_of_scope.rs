//@ expect: reject
//@ verdict: unknown
//@ mechanism: the default-method spelling of method_call_blanket_impl_other_trait_out_of_scope. `impl AssocTrait for S {}` does not define `holds`, so at `S` Rust runs `AssocTrait`'s DEFAULT body, the one trait in scope where `s.holds()` is written. The typed receiver lookup (`identity_typed::resolve_family_on_type`) asks only impl and inherent members whether they apply, so the default is invisible to it beside an impl member that applies: the one hit it finds is `<S as other::Other>::holds`, a trait not in scope there, and it binds that.
//@ accept-means: a method call in a program function's own clause was bound to another trait's method where Rust runs the in-scope trait's default body, and the function was credited on it.
//@ WHY IT IS FALSE: `s.holds()` is `AssocTrait`'s default, which is `false`, so `f`'s postcondition is `false`. Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `f verified ✓`, before D-161, and with either of D-161's halves knocked out: without the typed-lookup half the lookup binds `<S as other::Other>::holds` itself; without the sort-dispatch half the lookup refuses and the sort dispatch binds it.
//@ fixed-by: D-161 (the default at `S` is a candidate beside `Other`'s impl, and the call is refused; the sort dispatch refuses the family)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait AssocTrait {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

pub struct S;
impl AssocTrait for S {}

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

// WRONG: here `s.holds()` is <S as AssocTrait>::holds, the default, which is false.
#[ensures(s.holds())]
pub fn f(s: S) {}
