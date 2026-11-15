//@ expect: reject
//@ mechanism: the spelling of quantifier_binder_generic_param_view_read_as_every_integer_granted.rs with a
//@ mechanism: generic parameter the parser does not take for one (`Key`, not a single letter): the binder
//@ mechanism: gets no sort, is read at the integers, and `x@` as the value itself.
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

#[ensures(result == (exists<x: Key> x@ >= 256))]
pub fn f<Key: View<ViewTy = Int>>() -> bool {
    true
}
