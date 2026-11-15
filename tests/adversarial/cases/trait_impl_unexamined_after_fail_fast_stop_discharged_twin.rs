//@ expect: reject
//@ mechanism: the true twin of trait_impl_unexamined_after_fail_fast_stop: the only impl of
//@ mechanism: `Rd::rd` returns true, so `gen_read` and `go` claim nothing false. `bad` still fails
//@ mechanism: and the #3771 adaptive stop still fires before `<W as Rd>::rd`; the implementations
//@ mechanism: of contracted trait methods are verified after the stop, this one discharges the
//@ mechanism: contract, and both credits stand.
//@ fixed-by: D-94 (implementations of contracted trait methods are verified after the adaptive stop)
//@ accept-means: `bad` claims `result == 2` and returns 1.
//@ teeth: the one token that makes the grant undischarged separates this case from its twin. Were an impl left unexamined by the stop merely recorded undischarged, `gen_read` and `go` would be withdrawn here as well, although true.
//@ note: the fillers make the crate oversubscribe the adaptive budget at this wall; their credits are TRUE.
//@ timeout: 300
//@ also-verified: gen_read, go, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, <W as Rd>::rd
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

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go() -> bool {
    gen_read::<W>(&W)
}

// A validated failure: under an oversubscribed adaptive budget it stops the run.
#[ensures(result == 2u32)]
pub fn bad() -> u32 {
    1
}

#[ensures(result == 0u32)]
pub fn f0() -> u32 {
    0
}

#[ensures(result == 1u32)]
pub fn f1() -> u32 {
    1
}

#[ensures(result == 2u32)]
pub fn f2() -> u32 {
    2
}

#[ensures(result == 3u32)]
pub fn f3() -> u32 {
    3
}

#[ensures(result == 4u32)]
pub fn f4() -> u32 {
    4
}

#[ensures(result == 5u32)]
pub fn f5() -> u32 {
    5
}

#[ensures(result == 6u32)]
pub fn f6() -> u32 {
    6
}

#[ensures(result == 7u32)]
pub fn f7() -> u32 {
    7
}

#[ensures(result == 8u32)]
pub fn f8() -> u32 {
    8
}

#[ensures(result == 9u32)]
pub fn f9() -> u32 {
    9
}

#[ensures(result == 10u32)]
pub fn f10() -> u32 {
    10
}

#[ensures(result == 11u32)]
pub fn f11() -> u32 {
    11
}

// Restates the trait's clause, so its refinement goal is a tautology and the
// body is the only obligation that could find the `false`; the stop skips it.
impl Rd for W {
    #[ensures(result)]
    fn rd(&self) -> bool {
        true
    }
}
