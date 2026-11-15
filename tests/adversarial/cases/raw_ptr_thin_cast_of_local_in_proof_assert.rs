//@ expect: reject
//@ mechanism: a proof_assert's cast over a LOCAL is read at the type the body binds it at (a fat
//@ mechanism: pointer), so it is `thin`, not the identity.
//@ fixed-by: D-145
//@ accept-means: a proof_assert's cast over a local bound to a fat pointer is read as its operand.
//@ WHY THE CONTRACT IS FALSE: two slice pointers with one address and different lengths meet the
//@ WHY THE CONTRACT IS FALSE: precondition, and their thin casts are equal.
//@ teeth: a parse error at the merge base; `failed` after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p != q)]
pub fn f(p: *const [u8], q: *const [u8]) {
    let a = p;
    let b = q;
    proof_assert!(a as *const u8 != b as *const u8);
}
