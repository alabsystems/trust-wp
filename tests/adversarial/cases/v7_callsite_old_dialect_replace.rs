//@ expect: reject
//@ mechanism: `mem::replace` specified in the pre-Creusot dialect: `*p == v` is the value `p` is
//@ mechanism: left with, and the callee proves it so. The call site reads `*p` at the call, so the
//@ mechanism: caller learns that the entry value of its argument is `v`, and that the returned
//@ mechanism: `old(*p)` is `v` too.
//@ accept-means: the value `replace` hands back is the one it was asked to store.
//@ WHY THE CONTRACT IS FALSE: with *x = 1 at entry, `replace(x, 7)` returns 1.
//@ fixed-by: D-101
//@ teeth: MEASURED on d73d0571 (debug driver): `replace_caller verified`. On the D-101 tree: unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(*p == v && result == old(*p))]
pub fn replace(p: &mut u32, v: u32) -> u32 {
    let o = *p;
    *p = v;
    o
}

#[ensures(result == 7u32)]
pub fn replace_caller(x: &mut u32) -> u32 {
    replace(x, 7)
}
