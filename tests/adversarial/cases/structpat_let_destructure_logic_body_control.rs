//@ expect: verify
//@ mechanism: the true control of structpat_let_destructure_logic_body_reorder: `g` returns the
//@ mechanism: field `pick`'s binding names.
//@ accept-means: n/a (control).
//@ teeth: MEASURED on the merged tip 4e4613be: failed, exit 1 (the reviewer's ld02c) — the
//@ teeth: positional lowering made a TRUE contract unprovable.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[logic(open)]
pub fn pick(s: S) -> Int { pearlite! { let S { a: aa, b: _bb } = s; aa@ } }

#[requires(pick(s) == 5)]
#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 { match s { S { b: _b, a } => a } }
