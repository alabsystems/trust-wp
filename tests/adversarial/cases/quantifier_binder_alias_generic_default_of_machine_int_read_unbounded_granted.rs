//@ expect: reject
//@ mechanism: `type B<T = u8> = T;` read without arguments is `B<u8>`, which is `u8`, so Rust's
//@ mechanism: `exists<x: B> x@ >= 256` is false. D-205 asks whether an alias's TARGET holds a machine
//@ mechanism: integer, and `T` does not: the default a bare spelling reads is not looked at, so `B` is
//@ mechanism: not refused, the binder gets no range, and `f`, which returns true, is credited. The
//@ mechanism: defaulted spelling of quantifier_binder_module_alias_of_machine_int_read_unbounded_granted.rs.
//@ fixed-by: D-207 — REFUSED: an alias whose defaulted parameter holds a machine integer is among D-205's
//@ fixed-by: names (`callbacks::spelled_type_names::alias_holds_machine_int`).
//@ accept-means: `f` claims `result == (exists<x: u8> x@ >= 256)`, which is false, returns true,
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-206 in force.
//@ teeth: With D-207: REFUSED (`unknown`): `f`'s ensures fails to parse (`B`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub type B<T = u8> = T;

#[ensures(result == (exists<x: B> x@ >= 256))]
pub fn f() -> bool {
    true
}
