//@ expect: reject
//@ mechanism: the body's `use std::os::raw;` brings the module into the block the clause is read in
//@ mechanism: (D-195), and `raw::c_uchar` is an alias of `u8`, so Rust's
//@ mechanism: `exists<x: raw::c_uchar> x@ >= 256` is false. The binder gets no range and `f`, which
//@ mechanism: returns true, is credited. The block spelling of
//@ mechanism: quantifier_binder_module_import_alias_path_of_machine_int_read_unbounded_granted.rs.
//@ fixed-by: D-206 — REFUSED: a written type holding a path through a name the crate binds to a
//@ fixed-by: module or a crate (`core`, `std`, an imported `ffi`) is refused
//@ fixed-by: (`callbacks::spelled_type_names::module_names`, `spelled_types::first_module_path`).
//@ accept-means: `f` claims `result == (exists<x: u8> x@ >= 256)`, which is false, returns true,
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-205 in force.
//@ teeth: With D-206: REFUSED (`unknown`): `f`'s ensures fails to parse (the path).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (exists<x: raw::c_uchar> x@ >= 256))]
pub fn f() -> bool {
    use std::os::raw;
    true
}
