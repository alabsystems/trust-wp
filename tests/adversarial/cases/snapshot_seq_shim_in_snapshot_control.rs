//@ expect: verify
//@ mechanism: the TRUE twin of snapshot_seq_shim_in_program_context_returns_empty: the same
//@ mechanism: `Snapshot<Seq<T>>::push_back` and `concat` shims inside `snapshot!`, which never runs,
//@ mechanism: are read as the logical `push_back` and `concat` of the snapshot's value.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — verified before and after the shims are refused in program code.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn push_back_read() {
    let s: Snapshot<Seq<i32>> = snapshot!(Seq::empty());
    let t = snapshot!(s.push_back(1i32));
    proof_assert!(t.len() == 1);
}

#[ensures(true)]
pub fn concat_read() {
    let s: Snapshot<Seq<i32>> = snapshot!(Seq::singleton(2i32));
    let t = snapshot!(s.concat(Seq::singleton(1i32)));
    proof_assert!(t.len() == 2);
}
