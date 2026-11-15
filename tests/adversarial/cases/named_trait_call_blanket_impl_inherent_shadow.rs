//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: `AssocTrait::holds(s)` names the trait, so Rust's callee is the `AssocTrait` impl that applies at `S`: the BLANKET `impl<T: Marker> AssocTrait for T`. `S` also has an inherent `holds`. A lookup of `holds` over every definition of the name at `S`'s type that compares self types sees only the inherent one, and a call through a named trait bound to it: the path's trait was never consulted.
//@ fixed-by: D-160 (a call through a named trait is looked up among that trait's declaration and implementations only, and a blanket impl is a candidate wherever rustc's selection picks it)
//@ accept-means: a call written through a named trait was bound to an inherent method of the same name, and `f` was credited on it.
//@ WHY IT IS FALSE: `AssocTrait::holds(s)` is the blanket `holds`, which is `false`, so `f`'s postcondition is `false`. Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, `f verified ✓`, with both halves of the fix knocked out (the named-trait narrowing, and the selection-based applicability test read back to a self-type comparison); with only one half knocked out it is refused, and with neither it FAILS.
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
impl S {
    #[logic(open)]
    pub fn holds(self) -> bool {
        true
    }
}

// WRONG: `AssocTrait::holds(s)` is the blanket impl's `holds`, which is false.
#[ensures(AssocTrait::holds(s))]
pub fn f(s: S) {}
