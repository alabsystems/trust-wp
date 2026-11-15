//@ expect: verify
//@ mechanism: control: the assertion precedes the loop, so the loop's write to `*a` cannot reach it and the entry fact is kept
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32, n: u32) { proof_assert!((*a)@ == 0); let mut i = 0u32; #[invariant(i@ <= n@)] while i < n { *a = 7; i += 1; } }
