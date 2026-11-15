//@ expect: reject
//@ verdict: unknown
//@ refused-with: a `&mut` a parameter holds without being it has no placement
//@ mechanism: a `&mut` held in a field of a tuple parameter (`t: (&mut i32, i32)`), read as
//@ mechanism: `*t.0` under and outside `old(..)`: the dialect rule saw `t` inside `old`, and the
//@ mechanism: `*p -> ^p` rewrite reached only `*t`, so `*t.0` stayed the entry value.
//@ accept-means: `*t.0 == old(*t.0)` holds of a function that increments `*t.0`.
//@ WHY THE CONTRACT IS FALSE: `*t.0` outside `old` is the value it is left with, entry + 1.
//@ fixed-by: D-101
//@ teeth: MEASURED on d73d0571 (debug driver): `tuple_param_old verified`. On the D-101 tree the
//@ teeth: clause is refused by name.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*t.0 < 100i32)]
#[ensures(*t.0 == old(*t.0))]
pub fn tuple_param_old(t: (&mut i32, i32)) {
    *t.0 += 1;
}
