//@ expect: reject
//@ verdict: failed
//@ mechanism: the declaration-order twin of structpat_let_destructure_requires_reorder. Same
//@ mechanism: MEANING (`a == 5`), same body (returns `b`), fields written in DECLARATION order.
//@ mechanism: If the reordered twin verifies while this one fails, the order the two fields
//@ mechanism: were typed in decided the verdict.
//@ accept-means: the same as its twin — a precondition pinning a field the body does not return.
//@ WHY THE CONTRACT IS FALSE: the precondition pins `a`; `g` returns `b`. `S { b: 0, a: 5 }`
//@ WHY THE CONTRACT IS FALSE: satisfies it and returns 0.
//@ teeth: MEASURED on the merged tip 4e4613be: failed, exit 1 — while its reordered twin
//@ teeth: ACCEPTED, exit 0 (the reviewer's ld01d against ld01). The pair is the evidence.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[requires({ let S { b: _bb, a: aa } = s; aa@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 { match s { S { b, a: _a } => b } }
