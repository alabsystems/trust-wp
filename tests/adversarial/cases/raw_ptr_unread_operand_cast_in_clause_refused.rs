//@ expect: reject
//@ mechanism: a clause's cast whose operand type the classifier does not read (a field) stays a
//@ mechanism: pending marker, which the encoder refuses. Read as the identity, `s.p != s.q` would
//@ mechanism: prove the thin casts different.
//@ fixed-by: D-145
//@ accept-means: an unread clause cast is read as its operand (or dropped).
//@ WHY THE CONTRACT IS FALSE: two slice pointers with one address and different lengths meet the
//@ WHY THE CONTRACT IS FALSE: precondition, and their thin casts are equal.
//@ teeth: refused (`raw pointer cast ... was not classified`); a parse error at the merge base.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub p: *const [u8],
    pub q: *const [u8],
}

#[requires(s.p != s.q)]
#[ensures(s.p as *const u8 != s.q as *const u8)]
pub fn f(s: S) {}
