//@ expect: reject
//@ mechanism: a trait's default method verified once for every `Self`: `exists<x: Self> x@ >= 256` is
//@ mechanism: read at the integers with `x@` the value itself, holds, and the default body, which
//@ mechanism: returns true, is credited. An implementation for `u8` that takes the default would run
//@ mechanism: that body under a claim Rust reads as false. The generic spelling of
//@ mechanism: trait_contract_self_binder_exists_inherited_by_machine_int_impl_granted.rs.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a binder over a type the
//@ fixed-by: encoding carries by the integers ranges over a domain the solver may not assume is all
//@ fixed-by: of them (a domain predicate, or an uninterpreted sort), and `@` of a value of a generic
//@ fixed-by: type is an uninterpreted view, not the value itself.
//@ accept-means: `Tr::m` at `Self = u8` claims `result == false` in Rust's reading, returns true, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`Tr::m verified ✓`) with D-206 in force.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr: View<ViewTy = Int> + Sized {
    #[ensures(result == (exists<x: Self> x@ >= 256))]
    fn m() -> bool {
        true
    }
}
