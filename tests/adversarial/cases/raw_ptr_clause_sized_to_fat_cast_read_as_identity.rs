//@ expect: reject
//@ mechanism: a clause's `p as *const [u8]` from `*const [u8; 4]` is an unsizing coercion, which
//@ mechanism: ADDS a length; the clause classifier sees it untyped, and Creusot's rule reads any fat
//@ mechanism: target as the identity (sound for MIR `PtrToPtr`, which never unsizes). Read so, equal
//@ mechanism: thin pointers made the length-4 and length-8 fat pointers equal.
//@ fixed-by: D-145
//@ accept-means: a clause's sized-to-fat raw-pointer cast is read as its operand.
//@ WHY THE CONTRACT IS FALSE: `p` and `q` at one address meet the precondition; their fat pointers
//@ WHY THE CONTRACT IS FALSE: have lengths 4 and 8.
//@ teeth: ACCEPTED under the first draft of D-145 (Creusot's rule); a parse error at the merge base.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p as *const u8 == q as *const u8)]
#[ensures(p as *const [u8] == q as *const [u8])]
pub fn claims_equal(p: *const [u8; 4], q: *const [u8; 8]) {}
