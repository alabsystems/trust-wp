//@ expect: verify
//@ mechanism: THE over-refusal control the s82 fix exists to protect. A reordered enum-variant
//@ mechanism: pattern whose fields have the SAME type: nothing can mistype, so refusing it would
//@ mechanism: be a pure completeness loss on ordinary correct code. This contract is TRUE only
//@ mechanism: under the CORRECT binding, so it also proves the fix RESOLVES the order rather
//@ mechanism: than merely declining to guess.
//@ accept-means: n/a (control) — `aa` names `a`, the body returns `a`, the precondition pins it.
//@ teeth: n/a — over-refusal control. Read positionally it assumes `b == 5 && a == 7` and the
//@ teeth: body returns 7, so it does NOT verify while the defect is live.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub enum R { C { a: u32, b: u32 }, N }
#[requires(match r { R::C { b: bb, a: aa } => aa@ == 5 && bb@ == 7, R::N => false })]
#[ensures(result@ == 5)]
pub fn f(r: R) -> u32 { match r { R::C { a, b: _b } => a, R::N => 0 } }
