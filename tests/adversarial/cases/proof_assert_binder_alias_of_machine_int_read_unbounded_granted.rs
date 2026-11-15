//@ expect: reject
//@ mechanism: the assertion spelling of quantifier_binder_module_alias_of_machine_int_read_unbounded_granted.rs:
//@ mechanism: with `type Byte = u8;` no `Byte` reaches 256, so `proof_assert!(exists<x: Byte> x@ >= 256)`
//@ mechanism: is false; read with no range over the unbounded integers it holds.
//@ fixed-by: D-205 — REFUSED: a name the crate binds to a type holding a machine integer (an
//@ fixed-by: alias, an import, an associated type, an impl's `Self`) is refused wherever a clause
//@ fixed-by: spells it as a type (`callbacks::spelled_type_names::machine_int_alias_names`).
//@ accept-means: an assertion Rust reads as false is verified, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`proof_assert in creusot_test::f verified ✓`) with D-204 in
//@ teeth: force.
//@ teeth: With D-205: REFUSED (`unknown`): the assertion fails to parse (`Byte`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub type Byte = u8;

pub fn f() {
    proof_assert!(exists<x: Byte> x@ >= 256);
}
