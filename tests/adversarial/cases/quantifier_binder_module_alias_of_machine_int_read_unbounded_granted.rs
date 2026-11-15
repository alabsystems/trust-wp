//@ expect: reject
//@ mechanism: `type Byte = u8;` names `u8` under a new name, so Rust's `exists<x: Byte> x@ >= 256`
//@ mechanism: ranges over `u8` and is false. The contract parser reads a binder's type by its
//@ mechanism: SPELLING: `Byte` is no machine integer it knows (`quantifiers::machine_int`) and no
//@ mechanism: spelled name the crate shadows (D-202), so the binder gets no sort, no range is
//@ mechanism: stated (D-203), and `x@` reads it over the unbounded integers, where the quantifier
//@ mechanism: holds; `f`, which returns true, is credited. The sideways spelling of
//@ mechanism: quantifier_binder_machine_int_read_unbounded_granted.rs through an alias.
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
use creusot_std::prelude::*;

pub type Byte = u8;

#[ensures(result == (exists<x: Byte> x@ >= 256))]
pub fn f() -> bool {
    true
}
