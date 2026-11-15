//@ expect: reject
//@ mechanism: `use core::primitive::u8 as Byte;` binds `Byte` to the primitive `u8` in the type
//@ mechanism: namespace, so Rust's `exists<x: Byte> x@ >= 256` is false. The parser reads `Byte` by
//@ mechanism: its spelling, states no range, and `f`, which returns true, is credited. The import
//@ mechanism: spelling of quantifier_binder_module_alias_of_machine_int_read_unbounded_granted.rs.
//@ fixed-by: D-205 — REFUSED: a name the crate binds to a type holding a machine integer (an
//@ fixed-by: alias, an import, an associated type, an impl's `Self`) is refused wherever a clause
//@ fixed-by: spells it as a type (`callbacks::spelled_type_names::machine_int_alias_names`).
//@ accept-means: `f` claims `result == (exists<x: u8> x@ >= 256)`, which is false, returns true,
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-204 in force.
//@ teeth: With D-205: REFUSED (`unknown`): `f`'s ensures fails to parse (`Byte`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use core::primitive::u8 as Byte;
use creusot_std::prelude::*;

#[ensures(result == (exists<x: Byte> x@ >= 256))]
pub fn f() -> bool {
    true
}
