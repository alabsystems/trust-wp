//@ expect: verify
//@ mechanism: control: the loop lane now verifies its in-function assertions, and hands them the loop-exit premise it proved
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() { let mut i = 0u32; #[invariant(i@ <= 3)] while i < 3 { i += 1; } proof_assert!(i@ <= 3); }
