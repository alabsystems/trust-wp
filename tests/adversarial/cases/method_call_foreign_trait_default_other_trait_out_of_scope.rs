//@ expect: reject
//@ verdict: failed
//@ mechanism: `s.invariant()` where `creusot_std`'s `Invariant` is in scope (the prelude) and `impl Invariant for S {}` does not define `invariant`, so Rust runs `Invariant`'s default body, `true`. A local trait `other::Other`, not in scope there, also defines `invariant` for `S`. The collision family holds only this crate's definitions, so the typed receiver lookup (`identity_typed::resolve_family_on_type`) never sees the foreign trait or its default: its one hit is `<S as other::Other>::invariant`, and it binds that.
//@ accept-means: a method call was bound to a local trait not in scope where Rust selects a foreign trait's method, and the function was credited on it.
//@ WHY IT IS FALSE: `s.invariant()` is `Invariant`'s default, `true`, so `!s.invariant()` is `false` and so is `f`'s postcondition. Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `f verified ✓`. At D-163: rejected (`unknown`), the call refused.
//@ teeth: At D-208: `f FAILED ✗ (postcondition)`, a validated counterexample: the receiver lookup's pick `<S as other::Other>::invariant` is dropped before rustc is asked (D-196 item 3: `creusot_std`'s `Invariant` may apply at `S`), the encoder's dispatch refuses it too, and `s.invariant()` is read as `S`'s invariant, `true`.
//@ fixed-by: D-163 — the lookup's `<S as other::Other>::invariant` is kept only where rustc's type check of `f`'s `ensures` resolved `s.invariant()` to it; rustc resolved `Invariant`'s default, so the call is refused as the unresolved marker, which the encoder refuses before any sort dispatch reads it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;
impl Invariant for S {}

pub mod other {
    use creusot_std::prelude::*;
    pub trait Other {
        #[logic]
        fn invariant(self) -> bool;
    }
    impl Other for super::S {
        #[logic(open)]
        fn invariant(self) -> bool {
            false
        }
    }
}

// WRONG: here `s.invariant()` is creusot_std's `Invariant` default, which is true.
#[ensures(!s.invariant())]
pub fn f(s: S) {}
