//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: the contract parser read `e as T` as `e`, so `(x as u8)@ == x@` was proved as
//@ mechanism: `x@ == x@`. A cast is Rust's `as`: the value of `u8` congruent to `x` modulo 256.
//@ fixed-by: D-84 (contract casts lowered to Rust's `as`)
//@ accept-means: a contract whose cast truncates was proved about the untruncated operand;
//@ accept-means: false at x = 256
//@ teeth: verified with the lowering replaced by the operand; FAILED with it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((x as u8)@ == x@)]
pub fn f(x: u64) {}
