//@ expect: reject
//@ mechanism: the same lost capture write with a CONTRACT-FREE closure. No closure postcondition
//@ mechanism: exists to be mis-scoped, so the credit is the caller's `#[requires]` alone: the
//@ mechanism: by-value capture owner is left bound to its entry symbol across the call, and the
//@ mechanism: entry premise is still in force after the closure wrote the field.
//@ accept-means: the defect is not the closure contract's scope but the capture owner's state —
//@ accept-means: a mutating closure call advances nothing, so ANY entry premise about a captured
//@ accept-means: by-value local survives the call, contract on the closure or not.
//@ fixed-by: D-55
//@ WHY THE CONTRACT IS FALSE: `returns_entry_value_contractless((1, 0))` returns 9.
//@ teeth: ACCEPTED on this tree and on the campaign build tree's own engine binary (exit 0,
//@ teeth: `1 verified, 0 failed, 0 errors`). Twin of the contracted case, which also accepts;
//@ teeth: the pair separates the closure-postcondition scope from the capture-owner state.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(p.0@ == 1i32)]
#[ensures(result@ == 1i32)]
pub fn returns_entry_value_contractless(mut p: (i32, i32)) -> i32 {
    let mut clos = || {
        p.0 = 9i32;
    };
    clos();
    p.0
}
