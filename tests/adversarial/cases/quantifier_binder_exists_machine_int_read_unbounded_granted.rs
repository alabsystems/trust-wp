//@ expect: reject
//@ mechanism: quantifier_binder_machine_int_read_unbounded_granted.rs through `exists`: no `i8` is below
//@ mechanism: -128, so `exists<x: i8> x@ < -128` is false; read over the unbounded integers it holds,
//@ mechanism: and `f`, which returns true, is credited.
//@ fixed-by: D-203 — a machine-integer binder is read in its type's range: a premise of `forall`,
//@ fixed-by: a conjunct of `exists` (`quantifiers::MachineInt::range_of`).
//@ accept-means: `f` claims `result == false` in Rust's reading, returns true, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-202 in force.
//@ teeth: With D-203: `f FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (exists<x: i8> x@ < -128))]
pub fn f() -> bool {
    true
}
