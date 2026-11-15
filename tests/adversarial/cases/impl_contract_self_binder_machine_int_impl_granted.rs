//@ expect: reject
//@ mechanism: an impl for `u8` writes `result == (exists<x: Self> x@ >= 256)` on its own method,
//@ mechanism: false for `u8`. The parser gives the `Self` binder no range, the unbounded reading
//@ mechanism: holds, and the impl, which returns true, is credited. The crate is kept from exit 0
//@ mechanism: only by the refinement check, which refuses to compare a clause naming a binder of
//@ mechanism: no faithful sort; the per-function gate reads the credit.
//@ fixed-by: D-205 — REFUSED: a name the crate binds to a type holding a machine integer (an
//@ fixed-by: alias, an import, an associated type, an impl's `Self`) is refused wherever a clause
//@ fixed-by: spells it as a type (`callbacks::spelled_type_names::machine_int_alias_names`).
//@ accept-means: `<u8 as Tr>::m` is credited `verified` on a claim Rust reads as false.
//@ teeth: MEASURED: `<u8 as Tr>::m verified ✓`, then `trait refinement error`, exit 2, on a
//@ teeth: build that refused an alias's spelling and not `Self`'s.
//@ teeth: With D-205: REFUSED (`unknown`): `<u8 as Tr>::m`'s ensures fails to parse (`Self`), no credit.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    fn m() -> bool;
}

impl Tr for u8 {
    #[ensures(result == (exists<x: Self> x@ >= 256))]
    fn m() -> bool {
        true
    }
}
