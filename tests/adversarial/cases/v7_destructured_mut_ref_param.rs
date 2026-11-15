//@ expect: reject
//@ verdict: unknown
//@ refused-with: a `&mut` a parameter holds without being it has no placement
//@ mechanism: a `&mut` bound by a destructuring parameter pattern (`(p, q): (&mut i32, &mut
//@ mechanism: i32)`) read in a clause that names it under `old(..)`. The dialect rule is keyed by a
//@ mechanism: `&mut` PARAMETER's name, and the driver models neither reading of such a read
//@ mechanism: (`^p == *p + 1` was unknown): it read `*p` at entry and verified.
//@ accept-means: `*p == old(*p)` holds of a function that increments `*p`, in the dialect whose
//@ accept-means: `*p` is the value `p` is left with.
//@ WHY THE CONTRACT IS FALSE: read as contract-syntax.md reads a `&mut` "however the text reaches
//@ WHY THE CONTRACT IS FALSE: it", `*p` outside `old` is entry + 1.
//@ fixed-by: D-101 (a `&mut` a parameter holds without being it has no placement: refused)
//@ teeth: MEASURED on d73d0571 (debug driver): `destructured_old verified`. On the D-101 tree the
//@ teeth: clause is refused by name.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*p < 100i32)]
#[ensures(*p == old(*p))]
pub fn destructured_old((p, q): (&mut i32, &mut i32)) {
    *p += 1;
}
