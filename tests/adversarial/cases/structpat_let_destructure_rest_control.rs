//@ expect: verify
//@ mechanism: the true control of structpat_let_destructure_rest_reorder: `g` returns the field
//@ mechanism: the binding names. A rest pattern needs the declaration's field list to pad, so
//@ mechanism: this also guards against a refusal of `..` in `let` position.
//@ accept-means: n/a (control).
//@ teeth: MEASURED on the merged tip 4e4613be: failed, exit 1 — a TRUE contract, unprovable under
//@ teeth: the written-position reading; the other half of the pair.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[requires({ let S { a: aa, .. } = s; aa@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 { match s { S { b: _b, a } => a } }
