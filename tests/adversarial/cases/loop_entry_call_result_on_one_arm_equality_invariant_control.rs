//@ expect: verify
//@ mechanism: `let mut a = 0u32; if c { a = x.wrapping_sub(x); }` then `invariant(a == 0u32)`. The loop lane
//@ mechanism: resolves no pre-loop call on one path (D-243 (d)); the walker states `wrapping_sub`'s
//@ mechanism: postcondition under the arm's edge and `!c ==> a == 0` at the entry. The initiation needs the
//@ mechanism: split on `c`, which ay decides UNSAT and withholds (`proof-trusted`).
//@ accept-means: n/a (control) — `a` is 0 at the loop's entry on both paths.
//@ xfail: ay certification gap, not a trust-wp refusal; the parent verified it through its depth-first walk,
//@ xfail: which stated the call's postcondition at the entry on both paths.
//@ xfail-verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n < 10u32)]
pub fn f(x: u32, n: u32, c: bool) {
    let mut a = 0u32;
    if c {
        a = x.wrapping_sub(x);
    }
    let mut i = 0u32;
    #[invariant(a == 0u32)]
    while i < n {
        i += 1;
    }
}
