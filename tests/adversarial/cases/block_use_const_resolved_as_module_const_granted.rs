//@ expect: reject
//@ mechanism: a `use core::u8::MAX as K;` declared in a block binds `K` to 255 there; the crate root
//@ mechanism: declares `const K: u8 = 10`. Rust resolves `K` in the contract of `inner`, declared in
//@ mechanism: the block, through the import. A bare constant name is substituted by the value of the
//@ mechanism: one local constant of that name unless the name has another meaning somewhere in the
//@ mechanism: crate (`const_items::ambiguous_constant_names`), and the meanings it counts are local
//@ mechanism: items, module children and pattern bindings: an import declared in a BLOCK is none of
//@ mechanism: those, so `K` is read as 10 and `inner`, which returns 10, is verified against `result ==
//@ mechanism: 255`. The block spelling of D-111's `use core::u8::MAX as K` shape.
//@ fixed-by: D-195 — REFUSED: an import declared in a block counts among a constant name's meanings
//@ fixed-by: (`const_items::block_import_value_meanings`), so `K` has two and every clause spelling it
//@ fixed-by: is refused.
//@ accept-means: `inner` claims `result == K` with `K` = `u8::MAX` (255) and returns 10, and the crate
//@ accept-means: exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::inner verified ✓`). With D-195: `unknown` (`host::inner
//@ teeth: error: ... `__lfidU__ambiguous__constant__K` was not resolved`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub const K: u8 = 10;

pub fn host() -> u8 {
    #[allow(deprecated)]
    use core::u8::MAX as K;
    #[ensures(result == K)]
    fn inner() -> u8 {
        10
    }
    inner()
}
