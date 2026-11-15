//@ expect: reject
//@ mechanism: the crate root glob-imports module `t`, whose alias `u8 = u32` a glob import brings
//@ mechanism: into scope over the primitive, so Rust reads `300u32 as u8` in `f`'s contract as a cast
//@ mechanism: to `u32` (300). The contract parser reads the target by its spelling and lowers it to
//@ mechanism: the low eight bits (44); `f`, which returns 44, is credited.
//@ fixed-by: D-202 — REFUSED: a spelled type name the crate declares or imports with another
//@ fixed-by: meaning anywhere is refused wherever a clause spells it in a type position or as a
//@ fixed-by: path's head (`spelled_types`, `callbacks::spelled_type_names`).
//@ accept-means: `f` claims `result == 300`, returns 44, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-199 in force.
//@ teeth: With D-202: REFUSED (`unknown`): `f`'s ensures fails to parse (`u8`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod t {
    #[allow(non_camel_case_types)]
    pub type u8 = u32;
}
use t::*;

#[ensures(result == 300u32 as u8)]
pub fn f() -> u8 {
    44
}
