//@ expect: reject
//@ mechanism: cast_target_module_alias_shadows_primitive_granted.rs with the alias `type u8 = u32;`
//@ mechanism: declared in `host`'s block, around `inner`: Rust reads `300u32 as u8` in `inner`'s
//@ mechanism: contract as a cast to `u32` (300), and the contract parser, reading the target by its
//@ mechanism: spelling, lowers it to the low eight bits (44). `inner`, which returns 44, is credited.
//@ fixed-by: D-202 — REFUSED: a spelled type name the crate declares or imports with another
//@ fixed-by: meaning anywhere is refused wherever a clause spells it in a type position or as a
//@ fixed-by: path's head (`spelled_types`, `callbacks::spelled_type_names`).
//@ accept-means: `inner` claims `result == 300`, returns 44, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 with D-199 in force.
//@ teeth: With D-202: REFUSED (`unknown`): `host::inner`'s ensures fails to parse (`u8`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn host() -> u32 {
    #[allow(non_camel_case_types)]
    type u8 = u32;
    #[ensures(result == 300u32 as u8)]
    fn inner() -> u8 {
        44
    }
    inner()
}
