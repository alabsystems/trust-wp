//@ expect: reject
//@ mechanism: prophecy-store — a NON-final reborrow's final value linked to its parent's through the resolve-set shortcut (emit_prophecy_writebacks)
//@ accept-means: ^b1 == ^bor credited although ^b1 is 5 (written through b1) and ^bor is 1 (stored after b1 expired)
//@ teeth: verified on wp-s30 aae5ef9 (pre-fix); rejected after d245d8b
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn final_eq(bor: &mut i32) {
    let b1 = &mut *bor;
    *b1 = 5;
    *bor = 1;
    proof_assert!(^b1 == ^bor);
}
