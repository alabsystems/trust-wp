//@ expect: reject
//@ mechanism: the same field-order confusion inside a `proof_assert!` rather than a contract
//@ mechanism: clause. proof_assert_extract runs its OWN copy of the named-field rewrite
//@ mechanism: (proof_assert_extract/simplification/mod.rs), so it needs the same fix.
//@ accept-means: a proof_assert over a reordered pattern is discharged against a different
//@ accept-means: field's type.
//@ WHY THE CONTRACT IS FALSE: `aa` binds `a: u32`, and `g(E::C { a: 0, b: A })` asserts `0 == 5`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl A { #[logic(open)] pub fn view(self) -> Int { pearlite!{5} } }
pub enum E { C { a: u32, b: A }, N }
pub fn g(e: E) {
    proof_assert!(match e { E::C { b: bb, a: aa } => aa.view() == 5, E::N => true });
}
