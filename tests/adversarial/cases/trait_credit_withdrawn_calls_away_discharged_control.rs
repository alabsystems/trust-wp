//@ expect: verify
//@ mechanism: The isolating twin of trait_credit_withdrawn_calls_away: the same crate with the
//@ mechanism: impl of `Rd::rd` returning true instead of false, so the trait contract it inherits
//@ mechanism: is discharged and every claim here is TRUE. The two programs differ in that one
//@ mechanism: token, so this case is what says D-86 withdraws the credits that rest on an
//@ mechanism: undischarged contract rather than every caller of a generic function.
//@ fixed-by: D-86 (the trait-credit withdrawal walks the call graph)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
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
        true
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
// impl pays `Rd2::rd2` with a credit that stands exactly when `go`'s does.
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

// Reaches nothing that rests on `Rd::rd`.
#[ensures(result == 1u32)]
pub fn unrelated() -> u32 {
    1
}
