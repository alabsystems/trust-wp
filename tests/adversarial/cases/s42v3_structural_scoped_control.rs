//@ expect: verify
//@ mechanism: control: structural recursion on the strict subterm bound in the Cons arm still verifies with per-arm scoping
//@ fixed-by: s42 variant-recursion-scopes-v3
//@ accept-means: n/a (control)
//@ timeout: 300
//@ xfail: measured `unknown` (demoted: spec_axiom_dropped(1)). The recursion check ACCEPTS `len`
//@ xfail: (no recursion error); ay drops the enum-recursive definition axiom when encoding `g`.
//@ xfail: The scoping itself is pinned by structural_tests scoped_arm_binding_still_supports_structural_call.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum L {
    Cons(Int, Box<L>),
    Nil,
}
use L::*;

#[logic]
pub fn len(l: L) -> Int {
    pearlite! { match l { Cons(_, t) => len(*t) + 1, Nil => 0 } }
}

#[ensures(len(Nil) == 0)]
pub fn g() {}
