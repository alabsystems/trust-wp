//@ expect: reject
//@ mechanism: `let mut m = if c { 1u32 } else { 2u32 }`, a first loop that sets `m = 5`, then a second loop
//@ mechanism: claiming `invariant(m <= 2u32)`. The entry value the block-slice walker states for `m` (D-243) is
//@ mechanism: its value at the FIRST loop's entry; a premise reading it at the second loop's would initiate
//@ mechanism: that invariant.
//@ accept-means: an invariant is initiated from a local's value before an earlier loop that changes it.
//@ WHY THE CONTRACT IS FALSE: the second loop is entered with `m == 5`.
//@ teeth: rejected before and with D-243; it pins the scope of D-243 (e): a local a loop changes is stated only at the
//@ teeth: first loop's entry, for the premises of that loop's initiation.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(c: bool) {
    let mut m = if c { 1u32 } else { 2u32 };
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3 {
        m = 5;
        i += 1;
    }
    let mut j = 0u32;
    #[invariant(m <= 2u32)]
    while j < 3 {
        j += 1;
    }
}
