//@ expect: reject
//@ mechanism: the `forall` spelling of quantifier_binder_module_alias_of_machine_int_read_unbounded_granted.rs:
//@ mechanism: every `u8` is below 256, so Rust's `forall<x: Byte> x@ < 256` holds with
//@ mechanism: `type Byte = u8;`. Read with no range over the unbounded integers it is false, and
//@ mechanism: `f`, which returns false, is credited.
//@ fixed-by: D-205 — REFUSED: a name the crate binds to a type holding a machine integer (an
//@ fixed-by: alias, an import, an associated type, an impl's `Self`) is refused wherever a clause
//@ fixed-by: spells it as a type (`callbacks::spelled_type_names::machine_int_alias_names`).
//@ accept-means: `f` claims `result == (forall<x: u8> x@ < 256)`, which is true, returns false, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-204 in force.
//@ teeth: With D-205: REFUSED (`unknown`): `f`'s ensures fails to parse (`Byte`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub type Byte = u8;

#[ensures(result == (forall<x: Byte> x@ < 256))]
pub fn f() -> bool {
    false
}
