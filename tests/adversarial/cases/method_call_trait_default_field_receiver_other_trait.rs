//@ expect: reject
//@ verdict: unknown
//@ mechanism: method_call_trait_default_other_trait_out_of_scope with a FIELD receiver, whose Rust type the driver's typed receiver lookup does not read, so the call reaches the encoder's sort dispatch (`resolve_family_by_receiver`). That dispatch binds the one impl member whose nominal self sort is the receiver's: `<S as other::Other>::holds`. At `S` Rust runs `AssocTrait`'s default body (`impl AssocTrait for S {}`), the one trait in scope where `w.s.holds()` is written, and no impl member carries that default.
//@ accept-means: a method call on a field was bound by its solver sort to another trait's method where Rust runs the in-scope trait's default body, and the function was credited on it.
//@ WHY IT IS FALSE: `w.s.holds()` is `AssocTrait`'s default, which is `false`, so `f`'s postcondition is `false`. Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0 (`f verified ✓`), with D-161's sort-dispatch half knocked out, and rejected with its typed-lookup half knocked out: the typed lookup never reads a field receiver's type, so this case isolates the sort dispatch.
//@ fixed-by: D-161 (the sort dispatch refuses a family one of whose trait defaults runs at some impl)
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

pub struct W {
    pub s: S,
}

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

// WRONG: here `w.s.holds()` is <S as AssocTrait>::holds, the default, which is false.
#[ensures(w.s.holds())]
pub fn f(w: W) {}
