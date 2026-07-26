#![allow(unexpected_cfgs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression for #1264: by-value `self` methods must resolve `*self`
//! in std spec postconditions within proof_assert blocks.
//!
//! `Option::ok_or(self, err)` takes self by value. The postcondition uses
//! `match *self { Some(v) => ..., None => ... }`. When self is a fallback
//! arg, the spec is dropped and the proof_assert cannot verify.

use trust_wp::proof_assert;

fn by_value_self_ok_or() -> Result<i32, bool> {
    let none: Option<i32> = None;
    let err = none.ok_or(true);
    proof_assert!(err == Err(true));
    err
}

fn main() {
    let _ = by_value_self_ok_or();
}
