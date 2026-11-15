//@ expect: reject
//@ mechanism: the `exists` spelling of trait_contract_self_binder_inherited_by_machine_int_impl_granted.rs:
//@ mechanism: no `u8` reaches 256, so the inherited `result == (exists<x: Self> x@ >= 256)` is
//@ mechanism: `result == false` at the impl for `u8`; read with no range it is `result == true`, and
//@ mechanism: the impl, which returns true, is credited.
//@ fixed-by: D-205 — REFUSED: a name the crate binds to a type holding a machine integer (an
//@ fixed-by: alias, an import, an associated type, an impl's `Self`) is refused wherever a clause
//@ fixed-by: spells it as a type (`callbacks::spelled_type_names::machine_int_alias_names`).
//@ accept-means: `<u8 as Tr>::m` claims `result == false` in Rust's reading, returns true, and the
//@ accept-means: crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`<u8 as Tr>::m verified ✓`) on a build that
//@ teeth: refused an alias's spelling and not `Self`'s.
//@ teeth: With D-205: REFUSED (`unknown`): `<u8 as Tr>::m`'s inherited ensures fails to parse (`Self`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr: View<ViewTy = Int> + Sized {
    #[ensures(result == (exists<x: Self> x@ >= 256))]
    fn m() -> bool;
}

impl Tr for u8 {
    fn m() -> bool {
        true
    }
}
