//@ expect: reject
//@ mechanism: `Tr::m` claims `result == (forall<x: Self> x@ < 256)`; its impl for `u8` inherits
//@ mechanism: the clause, restated at the implementation with `Self` = `u8` (D-110), where every
//@ mechanism: `x` is below 256 and the claim is `result == true`. The contract parser reads a
//@ mechanism: binder's type by its SPELLING: `Self` is no machine integer it knows, so the binder
//@ mechanism: gets no range (D-203) and `x@` reads it over the unbounded integers, where the
//@ mechanism: quantifier is false; the impl, which returns false, is credited. The `Self` spelling
//@ mechanism: of quantifier_binder_module_alias_of_machine_int_read_unbounded_granted.rs.
//@ fixed-by: D-205 — REFUSED: a name the crate binds to a type holding a machine integer (an
//@ fixed-by: alias, an import, an associated type, an impl's `Self`) is refused wherever a clause
//@ fixed-by: spells it as a type (`callbacks::spelled_type_names::machine_int_alias_names`).
//@ accept-means: `<u8 as Tr>::m` claims `result == true` in Rust's reading, returns false, and the
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
    #[ensures(result == (forall<x: Self> x@ < 256))]
    fn m() -> bool;
}

impl Tr for u8 {
    fn m() -> bool {
        false
    }
}
