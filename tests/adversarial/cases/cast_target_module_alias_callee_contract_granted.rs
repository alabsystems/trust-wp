//@ expect: reject
//@ mechanism: cast_target_module_alias_shadows_primitive_granted.rs read at a CALL SITE. `g`'s contract
//@ mechanism: `result == 300u32 as u8` is, with the crate root's `type u8 = u32;`, a cast to `u32`
//@ mechanism: (300), and `g` returns 300. The contract parser reads the cast's target by its spelling
//@ mechanism: and lowers it to the low eight bits (44), so `caller`, which returns `g()` (300), is
//@ mechanism: credited with `result == 44`. (`g` itself is refuted on the same reading.)
//@ fixed-by: D-202 — REFUSED: a spelled type name the crate declares or imports with another
//@ fixed-by: meaning anywhere is refused wherever a clause spells it in a type position or as a
//@ fixed-by: path's head (`spelled_types`, `callbacks::spelled_type_names`).
//@ accept-means: `caller` claims `result == 44` and returns 300; ACCEPTED means that credit is printed.
//@ teeth: MEASURED: `caller verified ✓` (and `g FAILED`) with D-199 in force.
//@ teeth: With D-202: REFUSED (`unknown`): `g`'s ensures fails to parse (`u8`) and `caller`
//@ teeth: carries a fail-closed `false`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[allow(non_camel_case_types)]
type u8 = u32;

#[ensures(result == 300u32 as u8)]
pub fn g() -> u8 {
    300
}

#[ensures(result == 44u32)]
pub fn caller() -> u32 {
    g()
}
