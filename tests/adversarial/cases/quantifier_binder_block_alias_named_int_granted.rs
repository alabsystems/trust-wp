//@ expect: reject
//@ mechanism: quantifier_binder_module_alias_named_int_granted.rs with `type Int = u8;` declared in
//@ mechanism: `host`'s block: Rust's `forall<x: Int> x@ < 256` in `inner`'s contract ranges over `u8`
//@ mechanism: and holds, and the contract parser reads the binder by its spelling as the unbounded
//@ mechanism: integer sort, where it is false. `inner`, which returns false, is credited.
//@ fixed-by: D-202 — REFUSED: a spelled type name the crate declares or imports with another
//@ fixed-by: meaning anywhere is refused wherever a clause spells it in a type position or as a
//@ fixed-by: path's head (`spelled_types`, `callbacks::spelled_type_names`).
//@ accept-means: `inner` claims `result == true` in Rust's reading, returns false, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 with D-199 in force.
//@ teeth: With D-202: REFUSED (`unknown`): `host::inner`'s ensures fails to parse (`Int`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn host() -> bool {
    #[allow(dead_code)]
    type Int = u8;
    #[ensures(result == (forall<x: Int> x@ < 256))]
    fn inner() -> bool {
        false
    }
    inner()
}
