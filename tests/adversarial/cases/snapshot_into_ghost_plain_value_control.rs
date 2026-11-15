//@ expect: verify
//@ mechanism: `Snapshot::into_ghost` takes plain data out of a snapshot into ghost code, as Creusot's
//@ mechanism: (`T: Plain`); the ghost is the snapshot's value.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — verified before and after `into_ghost` asks `T: Plain`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f() {
    let s: Snapshot<u64> = snapshot!(7u64);
    let g: Ghost<u64> = s.into_ghost();
    proof_assert!(*g == 7u64);
}
