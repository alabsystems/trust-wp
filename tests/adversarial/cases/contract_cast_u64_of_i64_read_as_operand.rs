//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ mechanism: the contract parser read `e as T` as `e`, so `(y as u64)@ == y@` was proved as
//@ mechanism: `y@ == y@`. A sign-changing cast reinterprets the bits: `-1i64 as u64` is `u64::MAX`.
//@ fixed-by: D-84 (contract casts lowered to Rust's `as`)
//@ accept-means: a contract whose cast wraps a negative value was proved about the operand;
//@ accept-means: false at y = -1
//@ teeth: verified with the lowering replaced by the operand; FAILED with it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((y as u64)@ == y@)]
pub fn g(y: i64) {}
