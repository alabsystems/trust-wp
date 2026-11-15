//@ expect: reject
//@ mechanism: a credit that rests, through ordinary calls, on a generic caller's withdrawn
//@ mechanism: trait grant kept standing. The impl of `Rd::rd` inherits `result` and returns
//@ mechanism: false, so the trait contract is undischarged and `gen_read`'s grant is withdrawn;
//@ mechanism: `go` and `go2` reach it one and two plain calls away, `<W as Rd2>::rd2`'s body
//@ mechanism: pays `Rd2::rd2` with `go`'s contract, so `gen_read2` and `go3` reach it through a
//@ mechanism: second trait whose own impl never failed, and `pa_user`'s assertion rests on `go`.
//@ fixed-by: D-86 (the trait-credit withdrawal walks the call graph)
//@ accept-means: `go`, `go2`, `gen_read2` and `go3` all claim `result` and every one of them returns false; `pa_user` asserts a value that is false.
//@ teeth: with the grant ledger alone only `gen_read` is withdrawn and `go`, `go2`, `gen_read2`, `go3` stand `verified ✓`, and `pa_user`'s assertion stands `verified ✓`.
//@ also-verified: unrelated
//@ refused-with: pa_user error: verdict withdrawn - through `go` -> `gen_read`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

// Inherits `result` verbatim; the body is the only thing that could pay it.
impl Rd for W {
    fn rd(&self) -> bool {
        false
    }
}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go() -> bool {
    gen_read::<W>(&W)
}

#[ensures(result)]
pub fn go2() -> bool {
    go()
}

pub trait Rd2 {
    #[ensures(result)]
    fn rd2(&self) -> bool;
}

// Its body discharges the inherited `result` with `go`'s contract, so this
// impl pays `Rd2::rd2` with a credit that does not stand.
impl Rd2 for W {
    fn rd2(&self) -> bool {
        go()
    }
}

#[ensures(result)]
pub fn gen_read2<T: Rd2>(t: &T) -> bool {
    t.rd2()
}

#[ensures(result)]
pub fn go3() -> bool {
    gen_read2::<W>(&W)
}

pub fn pa_user() {
    let b = go();
    proof_assert!(b);
}

// Reaches nothing that rests on `Rd::rd`: its credit is TRUE and stands.
#[ensures(result == 1u32)]
pub fn unrelated() -> u32 {
    1
}
