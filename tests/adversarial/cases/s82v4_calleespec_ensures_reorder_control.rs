//@ expect: verify
//@ mechanism: the over-refusal half of the callee-spec arm. `get`'s `#[ensures]` writes its
//@ mechanism: fields reordered (`S { a: aa, b: _bb }` on `struct S { b, a }`) and therefore
//@ mechanism: means `a`; `caller` claims 5, which the precondition pins `a` at. TRUE under the
//@ mechanism: declared reading and NOT provable under the source-order one. It is also the
//@ mechanism: control that would catch the s82 v4 encoder placement gate over-refusing this
//@ mechanism: route: a refusal here reads as `unknown`, not as a verified proof.
//@ accept-means: n/a (control) — both contracts are TRUE.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub b: u32,
    pub a: u32,
}

#[ensures(match s { S { a: aa, b: _bb } => result@ == aa@ })]
pub fn get(s: S) -> u32 {
    match s {
        S { b: _b, a } => a,
    }
}

#[requires(s.a@ == 5 && s.b@ == 0)]
#[ensures(result@ == 5)]
pub fn caller(s: S) -> u32 {
    get(s)
}
