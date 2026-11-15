//@ expect: reject
//@ mechanism: `std::os::raw::c_uchar` is an alias of `u8`, so Rust's
//@ mechanism: `forall<x: std::os::raw::c_uchar> x@ < 256` holds. Read with no range over the unbounded
//@ mechanism: integers it is false, and `f`, which returns false, is credited. The `forall` spelling
//@ mechanism: of quantifier_binder_foreign_alias_path_of_machine_int_read_unbounded_granted.rs.
//@ fixed-by: D-206 — REFUSED: a written type holding a path through a name the crate binds to a
//@ fixed-by: module or a crate (`core`, `std`, an imported `ffi`) is refused
//@ fixed-by: (`callbacks::spelled_type_names::module_names`, `spelled_types::first_module_path`).
//@ accept-means: `f` claims `result == (forall<x: u8> x@ < 256)`, which is true, returns false, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-205 in force.
//@ teeth: With D-206: REFUSED (`unknown`): `f`'s ensures fails to parse (the path).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (forall<x: std::os::raw::c_uchar> x@ < 256))]
pub fn f() -> bool {
    false
}
