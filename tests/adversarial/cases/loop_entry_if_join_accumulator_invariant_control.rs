//@ expect: verify
//@ mechanism: `let mut m = if c { 1u32 } else { 0u32 }` and a loop that increments `m` under
//@ mechanism: `invariant(m <= i + 1u32)`: the initiation reads `m`'s entry value, a join symbol the block-slice
//@ mechanism: walker states for the first loop's entry although the loop changes `m` (D-243); preservation
//@ mechanism: reads the pass's value and is not given it.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(c: bool) -> u32 {
    let mut m = if c { 1u32 } else { 0u32 };
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    #[invariant(m <= i + 1u32)]
    while i < 3 {
        m += 1;
        i += 1;
    }
    m
}
