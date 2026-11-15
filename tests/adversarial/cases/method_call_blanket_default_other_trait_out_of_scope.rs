//@ expect: reject
//@ verdict: unknown
//@ mechanism: method_call_trait_default_other_trait_out_of_scope through a BLANKET impl: `impl<T: Marker> AssocTrait for T {}` does not define `holds`, so at `S` (a `Marker`) Rust runs `AssocTrait`'s default body. The blanket impl has no member of the `holds` family, so the typed receiver lookup's applicability test never asks about it, and the one hit is `<S as other::Other>::holds`, a trait not in scope where `s.holds()` is written.
//@ accept-means: a method call in a program function's own clause was bound to another trait's method where Rust runs a default body through a blanket impl, and the function was credited on it.
//@ WHY IT IS FALSE: `s.holds()` is `AssocTrait`'s default, which is `false`, so `f`'s postcondition is `false`. Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `f verified ✓`, before D-161, and with either of D-161's halves knocked out.
//@ fixed-by: D-161 (the default the blanket impl runs at `S` is a candidate beside `Other`'s impl, and the call is refused; the sort dispatch refuses the family)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Marker {}

pub trait AssocTrait {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

impl<T: Marker> AssocTrait for T {}

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

// WRONG: here `s.holds()` is <S as AssocTrait>::holds, the default through the blanket impl, which is false.
#[ensures(s.holds())]
pub fn f(s: S) {}
