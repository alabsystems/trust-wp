//@ expect: reject
//@ mechanism: `x@` of a value of a generic parameter is read as the value itself, so two values with
//@ mechanism: equal views are equal and `f`, which returns true, is credited for every `T`. A type
//@ mechanism: whose view forgets part of its value has two values with one view, where the claim is
//@ mechanism: `result == false`.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a binder over a type the
//@ fixed-by: encoding carries by the integers ranges over a domain the solver may not assume is all
//@ fixed-by: of them (a domain predicate, or an uninterpreted sort), and `@` of a value of a generic
//@ fixed-by: type is an uninterpreted view, not the value itself.
//@ accept-means: `f` at a type with a non-injective view claims `result == false` for two such values,
//@ accept-means: returns true, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-206 in force.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (x@ == y@ ==> x == y))]
pub fn f<T: View<ViewTy = Int>>(x: T, y: T) -> bool {
    true
}
