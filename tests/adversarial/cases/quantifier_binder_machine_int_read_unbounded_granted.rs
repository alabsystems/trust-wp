//@ expect: reject
//@ mechanism: `forall<x: u8> x@ < 256` ranges over the 256 values of `u8` and holds. The contract
//@ mechanism: parser maps every machine-integer binder type to the unbounded integer sort
//@ mechanism: (`quantifiers::type_annotation_sort`: `u8`..`u128`, `i8`..`i128`, `usize`, `isize` are
//@ mechanism: `Int`) and keeps no range for the bound variable, so the quantifier is read over every
//@ mechanism: integer, where it is false: `f`, which returns false, is credited against a contract
//@ mechanism: that says it returns true. The honoured twin
//@ mechanism: quantifier_binder_machine_int_honoured_control.rs, which returns true, is refuted.
//@ fixed-by: D-203 — a machine-integer binder is read in its type's range: a premise of `forall`,
//@ fixed-by: a conjunct of `exists` (`quantifiers::MachineInt::range_of`).
//@ accept-means: `f` claims `result == true` in Rust's (and Creusot's) reading, returns false, and the
//@ accept-means: crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-199 in force.
//@ teeth: With D-203: `f FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (forall<x: u8> x@ < 256))]
pub fn f() -> bool {
    false
}
