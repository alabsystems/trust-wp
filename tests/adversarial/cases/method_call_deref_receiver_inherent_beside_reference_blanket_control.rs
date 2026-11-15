//@ expect: verify
//@ mechanism: control: `(*a).invariant(b)` with `a: &mut A` (the shape `#[maintains((mut a).invariant(b,
//@ mechanism: c))]` expands to). The receiver `*a` has type `A`, where Rust's method lookup starts
//@ mechanism: and finds `A`'s inherent `invariant` by value; the prelude's blanket `Invariant for
//@ mechanism: &mut T` is a method of a type the lookup never tries. `b` holds, so the claim does.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED refused before D-201, which typed `*a` as `&mut A`)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A {}
impl A {
    #[logic(open)]
    pub fn invariant(self, b: bool) -> bool {
        pearlite! { b }
    }
}

#[requires(b)]
#[ensures((*a).invariant(b))]
pub fn f(a: &mut A, b: bool) {}
