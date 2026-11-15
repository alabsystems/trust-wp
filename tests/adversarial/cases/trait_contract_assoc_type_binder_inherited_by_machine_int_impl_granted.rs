//@ expect: reject
//@ mechanism: `Tr::m` claims `result == (forall<x: Self::Out> x@ < 256)`; the impl for `S` sets
//@ mechanism: `type Out = u8;` and inherits the clause, true there. The parser reads the binder
//@ mechanism: type `Self::Out` by its spelling, states no range, and the impl, which returns false,
//@ mechanism: is credited. The associated-type spelling of
//@ mechanism: trait_contract_self_binder_inherited_by_machine_int_impl_granted.rs.
//@ fixed-by: D-205 — REFUSED: a name the crate binds to a type holding a machine integer (an
//@ fixed-by: alias, an import, an associated type, an impl's `Self`) is refused wherever a clause
//@ fixed-by: spells it as a type (`callbacks::spelled_type_names::machine_int_alias_names`).
//@ accept-means: `<S as Tr>::m` claims `result == true` in Rust's reading, returns false, and the
//@ accept-means: crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`<S as Tr>::m verified ✓`) on a build that
//@ teeth: refused an alias's spelling and not `Self`'s.
//@ teeth: With D-205: REFUSED (`unknown`): `<S as Tr>::m`'s inherited ensures fails to parse (`Out`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    type Out: View<ViewTy = Int>;
    #[ensures(result == (forall<x: Self::Out> x@ < 256))]
    fn m() -> bool;
}

pub struct S;
impl Tr for S {
    type Out = u8;
    fn m() -> bool {
        false
    }
}
