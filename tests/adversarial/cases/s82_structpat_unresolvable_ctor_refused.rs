//@ expect: reject
//@ verdict: unknown
//@ refused-with: cannot place the fields of
//@ mechanism: the FAIL-CLOSED half of the s82 fix. Two enums declare a variant spelled `C` with
//@ mechanism: the same field NAMES in opposite declaration order, and the contract spells the
//@ mechanism: variant unqualified (it is in scope by `use`). trust-wp parses contract TEXT, so
//@ mechanism: the spelling alone does not say which `C` is meant, and the two answers place
//@ mechanism: `aa` at different indices. There is no safe guess: the old source-order fallback
//@ mechanism: would have bound `aa` to whichever field happened to be written second.
//@ accept-means: the driver guessed a field order it could not establish — which is the whole
//@ accept-means: s82 defect, just with a different reason for not knowing.
//@ WHY THE CONTRACT IS FALSE: read as written (`m1::E`), the precondition pins `a` and the body
//@ WHY THE CONTRACT IS FALSE: returns `b`; `f(C { a: 5, b: 0 })` returns 0. Read as `m2::E` it
//@ WHY THE CONTRACT IS FALSE: pins `b` instead and the postcondition follows, so a guess that
//@ WHY THE CONTRACT IS FALSE: lands on `m2` proves a false contract.
//@ teeth: the rejection is trust-wp's own named refusal — `refused-with:` pins the refusal text
//@ teeth: to one of trust-wp's own output lines, so a rustc compile error cannot stand in. The
//@ teeth: crate compiles: both enums are legal Rust and the unqualified `C` is in scope. The
//@ teeth: verdict is `unknown` rather than `error` because the refusal is COUNTED against the
//@ teeth: function (`0 verified, 0 failed, 1 errors`), which is how the classifier reads a
//@ teeth: per-function refusal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m1 {
    pub enum E { C { a: u32, b: u32 }, N }
}
pub mod m2 {
    pub enum E { C { b: u32, a: u32 }, N }
}

use m1::E::{C, N};

#[requires(match e { C { b: bb, a: aa } => aa@ == 5, N => false })]
#[ensures(result@ == 5)]
pub fn f(e: m1::E) -> u32 {
    match e { m1::E::C { a: _a, b } => b, m1::E::N => 0 }
}
