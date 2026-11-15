//@ expect: reject
//@ mechanism: the crate root declares `type u8 = u32;`, so Rust reads `u8::MAX` in `f`'s contract as
//@ mechanism: `u32::MAX`. trust-wp reads the path by its spelling as the primitive's bound, 255, and
//@ mechanism: `f`, which returns 255, is credited. The honoured twin
//@ mechanism: primitive_assoc_const_module_alias_shadows_honoured_control.rs, which returns
//@ mechanism: `u32::MAX`, is refuted: the verdicts are inverted.
//@ fixed-by: D-202 — REFUSED: a spelled type name the crate declares or imports with another
//@ fixed-by: meaning anywhere is refused wherever a clause spells it in a type position or as a
//@ fixed-by: path's head (`spelled_types`, `callbacks::spelled_type_names`).
//@ accept-means: `f` claims `result == u32::MAX`, returns 255, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-199 in force.
//@ teeth: With D-202: REFUSED (`unknown`): `f`'s ensures fails to parse (`u8::MAX`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[allow(non_camel_case_types)]
type u8 = u32;

#[ensures(result == u8::MAX)]
pub fn f() -> u8 {
    255
}
