//@ expect: reject
//@ mechanism: the crate root declares `type u8 = u32;`, which shadows the primitive `u8` in the
//@ mechanism: type namespace, so Rust reads `300u32 as u8` in `f`'s contract as a cast to `u32`: 300.
//@ mechanism: The contract parser reads a cast's target by its SPELLING (`casts::cast_target`) and
//@ mechanism: lowers `as u8` to the low eight bits, 44, so `f`, which returns 44, is credited. The
//@ mechanism: honoured twin cast_target_module_alias_shadows_primitive_honoured_control.rs, which
//@ mechanism: returns 300, is refuted: the verdicts are inverted.
//@ fixed-by: D-202 — REFUSED: a spelled type name the crate declares or imports with another
//@ fixed-by: meaning anywhere is refused wherever a clause spells it in a type position or as a
//@ fixed-by: path's head (`spelled_types`, `callbacks::spelled_type_names`).
//@ accept-means: `f` claims `result == 300` (the cast is to `u32`), returns 44, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-199 in force.
//@ teeth: With D-202: REFUSED (`unknown`): `f`'s ensures fails to parse (`u8`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[allow(non_camel_case_types)]
type u8 = u32;

#[ensures(result == 300u32 as u8)]
pub fn f() -> u8 {
    44
}
