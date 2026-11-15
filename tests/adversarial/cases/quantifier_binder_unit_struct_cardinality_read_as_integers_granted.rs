//@ expect: reject
//@ mechanism: `U` is a unit struct, with one value, so Rust's `forall<a: U, b: U> a == b` holds. The
//@ mechanism: binder is carried by the unbounded integers (D-7), where it is false, and `f`, which
//@ mechanism: returns false, is credited.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a binder over a type the
//@ fixed-by: encoding carries by the integers ranges over a domain the solver may not assume is all
//@ fixed-by: of them (a domain predicate, or an uninterpreted sort), and `@` of a value of a generic
//@ fixed-by: type is an uninterpreted view, not the value itself.
//@ accept-means: `f` claims `result == true` in Rust's reading, returns false, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-206 in force.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct U;

#[ensures(result == (forall<a: U, b: U> a == b))]
pub fn f() -> bool {
    false
}
