//@ expect: verify
//@ mechanism: control: the loop only READS the parameter, so its entry fact still holds after the loop
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32, n: u32) { let mut i = 0u32; #[invariant(i@ <= n@)] while i < n { i += 1; } proof_assert!((*a)@ == 0); }
