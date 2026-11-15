//@ expect: reject
//@ mechanism: a binder over a generic parameter: values are carried by the unbounded integers (D-7)
//@ mechanism: and `x@` of a value of `T` is read as the value itself, so `exists<x: T> x@ >= 256` holds
//@ mechanism: and `f`, which returns true, is credited for every `T`. At `T = u8` no value's view
//@ mechanism: reaches 256 and the claim is false.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a binder over a type the
//@ fixed-by: encoding carries by the integers ranges over a domain the solver may not assume is all
//@ fixed-by: of them (a domain predicate, or an uninterpreted sort), and `@` of a value of a generic
//@ fixed-by: type is an uninterpreted view, not the value itself.
//@ accept-means: `f::<u8>` claims `result == false` in Rust's reading, returns true, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-206 in force.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (exists<x: T> x@ >= 256))]
pub fn f<T: View<ViewTy = Int>>() -> bool {
    true
}
