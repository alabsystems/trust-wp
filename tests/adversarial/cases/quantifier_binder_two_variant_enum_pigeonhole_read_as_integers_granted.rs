//@ expect: reject
//@ mechanism: `E` has two values, so of any three one pair is equal and Rust's
//@ mechanism: `forall<a: E, b: E, c: E> a == b || b == c || a == c` holds. Carried by the unbounded
//@ mechanism: integers (D-7) it is false, and `f`, which returns false, is credited.
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

pub enum E {
    A,
    B,
}

#[ensures(result == (forall<a: E, b: E, c: E> a == b || b == c || a == c))]
pub fn f() -> bool {
    false
}
