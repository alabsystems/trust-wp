//@ expect: reject
//@ mechanism: a glob `use core::u8::*;` declared in a block brings `MAX` (255) into the block; the
//@ mechanism: crate root declares `const MAX: u8 = 10`. A glob in an inner scope shadows an outer item,
//@ mechanism: so Rust resolves `MAX` in the contract of `inner`, declared in the block, to `u8::MAX`.
//@ mechanism: The constant table counts no import declared in a block among a name's meanings, reads
//@ mechanism: `MAX` as the root's 10, and `inner`, which returns 10, is verified against `result ==
//@ mechanism: 255`. The glob spelling of block_use_const_resolved_as_module_const_granted.rs.
//@ fixed-by: D-195 — REFUSED: a glob declared in a block counts every child of its module among the
//@ fixed-by: names' meanings (`const_items::block_import_value_meanings`), so `MAX` has two and is
//@ fixed-by: refused.
//@ accept-means: `inner` claims `result == MAX` with `MAX` = `u8::MAX` (255) and returns 10, and the
//@ accept-means: crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::inner verified ✓`). With D-195: `unknown` (`host::inner
//@ teeth: error: ... `__lfidU__ambiguous__constant__MAX` was not resolved`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub const MAX: u8 = 10;

pub fn host() -> u8 {
    #[allow(unused_imports, deprecated)]
    use core::u8::*;
    #[ensures(result == MAX)]
    fn inner() -> u8 {
        10
    }
    inner()
}
