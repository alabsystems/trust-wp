//@ expect: reject
//@ also-verified: g
//@ mechanism: trait_path_call_read_as_inherent_method_granted.rs read at a CALL SITE: `g`'s contract
//@ mechanism: `result == Tr1::m(s)` is Tr1's default (10) and `g` returns 10, a true credit. A
//@ mechanism: caller reads `g`'s contract as text whose `Tr1::m(s)` is typed on its first argument
//@ mechanism: (`identity_typed::resolve_family_calls_in_text`) with no regard for the trait named, so
//@ mechanism: it reads the inherent `m` (0) and `caller`, which returns `g(s)` (10), is credited
//@ mechanism: with `result == 0`.
//@ fixed-by: D-196 — the callee-text resolver reads `Tr::m(x)` among Tr's own definitions
//@ fixed-by: (`identity_typed::qualified_path_rewrite`), as the owner's resolver does.
//@ accept-means: `caller` claims `result == 0` and returns 10; ACCEPTED means that credit is printed.
//@ teeth: MEASURED: `caller verified ✓` (and `g FAILED`, the owner-side reading of the same
//@ teeth: defect) with D-195 in force.
//@ teeth: With D-196: `g verified ✓` (true) and `caller FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;

pub trait Tr1 {
    #[logic(open)]
    fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}
impl Tr1 for S {}

impl S {
    #[logic(open)]
    pub fn m(self) -> u32 {
        pearlite! { 0u32 }
    }
}

#[ensures(result == Tr1::m(s))]
pub fn g(s: S) -> u32 {
    let _ = s;
    10
}

#[ensures(result == 0u32)]
pub fn caller(s: S) -> u32 {
    g(s)
}
