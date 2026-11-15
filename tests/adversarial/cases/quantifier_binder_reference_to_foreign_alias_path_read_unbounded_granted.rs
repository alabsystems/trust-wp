//@ expect: reject
//@ mechanism: a binder over references to `core::ffi::c_uchar`, an alias of `u8`: no referent reaches
//@ mechanism: 256, so Rust's `exists<r: &core::ffi::c_uchar> (*r)@ >= 256` is false. D-204 states a
//@ mechanism: referent's range only for a machine integer it reads by its spelling; this one gets
//@ mechanism: none, and `f`, which returns true, is credited. The reference spelling of
//@ mechanism: quantifier_binder_foreign_alias_path_of_machine_int_read_unbounded_granted.rs.
//@ fixed-by: D-206 — REFUSED: a written type holding a path through a name the crate binds to a
//@ fixed-by: module or a crate (`core`, `std`, an imported `ffi`) is refused
//@ fixed-by: (`callbacks::spelled_type_names::module_names`, `spelled_types::first_module_path`).
//@ accept-means: `f` claims `result == (exists<r: &u8> (*r)@ >= 256)`, which is false, returns true,
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-205 in force.
//@ teeth: With D-206: REFUSED (`unknown`): `f`'s ensures fails to parse (the path).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (exists<r: &core::ffi::c_uchar> (*r)@ >= 256))]
pub fn f() -> bool {
    true
}
