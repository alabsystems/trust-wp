//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: isolating twin of method_call_blanket_impl_sole_candidate_control.rs: the blanket `AssocTrait::holds` is `false`. The blanket impl is the one definition rustc's selection picks at `S`; `U`'s inherent `holds` (`true`) is on another type and must not be read as the call.
//@ fixed-by: D-160 (the blanket impl is bound where it is the one candidate; before, the call was refused)
//@ accept-means: `s.holds()` was bound to a `holds` that does not apply at `S`, or the blanket impl's body was not read.
//@ WHY IT IS FALSE: `s.holds()` is the blanket `holds`, which is `false`, so `f`'s postcondition is `false`. Creusot's `vc_f` is invalid.
//@ teeth: prospective for a lookup that binds by name alone; MEASURED `unknown` with D-160's applicability test knocked out, beside its twin's over-refusal, so the pair isolates the one resolution.
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

pub struct U;
impl U {
    #[logic(open)]
    pub fn holds(self) -> bool {
        true
    }
}

// WRONG: `s.holds()` is the blanket impl's `holds`, which is false.
#[ensures(s.holds())]
pub fn f(s: S) {}
