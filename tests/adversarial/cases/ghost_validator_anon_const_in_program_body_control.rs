//@ expect: verify
//@ mechanism: the program-context ghost validator reads the type of every expression it visits against
//@ mechanism: the typeck results of the body it walks, but an array length, a repeat count or a const
//@ mechanism: generic argument is an anonymous constant, typechecked apart from that body. Reading the
//@ mechanism: type of its literal was an ICE ("node_type: no type for node"), which refused every body
//@ mechanism: that spells `[0u8; 2]` or `size_of::<[T; 2]>()` (should_succeed `lang/size_of.rs`).
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — an ICE (exit 101) with the validator walking into anonymous constants, verified
//@ teeth: once it leaves each to its own body-owner visit.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn repeat() {
    let _a: [u8; 2] = [7u8; 2];
}

#[ensures(true)]
pub fn sized<T>() {
    let _n = core::mem::size_of::<[T; 2]>();
}
