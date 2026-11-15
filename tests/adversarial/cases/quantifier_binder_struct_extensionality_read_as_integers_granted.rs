//@ expect: reject
//@ mechanism: `P` has one `bool` field and no other state, so two values with equal fields are equal
//@ mechanism: and Rust's `exists<p: P, q: P> p.a == q.a && p != q` is false. Were a struct binder carried by
//@ mechanism: the unbounded integers (D-7), two values could share a field and differ, and `f`,
//@ mechanism: which returns true, would be credited.
//@ fixed-by: n/a (never accepted: a sideways guard of
//@ fixed-by: quantifier_binder_unit_struct_cardinality_read_as_integers_granted.rs)
//@ accept-means: `f` claims `result == false` in Rust's reading, returns true, and the crate exits 0.
//@ teeth: not shown: `f unknown (quantifier-unhandled)` with D-206 in force: the quantifier is left
//@ teeth: undecided, where a unit struct's is read false.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub a: bool,
}

#[ensures(result == (exists<p: P, q: P> p.a == q.a && p != q))]
pub fn f() -> bool {
    true
}
