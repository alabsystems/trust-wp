//@ expect: reject
//@ mechanism: `()` has one value, so Rust's `forall<a: (), b: ()> a == b` holds. Were the binder
//@ mechanism: carried by the unbounded integers (D-7) the quantifier would be false there, and `f`,
//@ mechanism: which returns false, credited.
//@ fixed-by: n/a (never accepted: a sideways guard of
//@ fixed-by: quantifier_binder_unit_struct_cardinality_read_as_integers_granted.rs)
//@ accept-means: `f` claims `result == true` in Rust's reading, returns false, and the crate exits 0.
//@ teeth: not shown: `f FAILED ✗ (postcondition)` with D-206 in force, and so is its true twin
//@ teeth: (`result == true`): the quantifier is decided neither way, where a unit struct's is read false.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (forall<a: (), b: ()> a == b))]
pub fn f() -> bool {
    false
}
