//@ expect: reject
//@ mechanism: the same field-order confusion in `#[requires]` rather than `#[ensures]`, and by
//@ mechanism: VALUE rather than by type: both variant fields are u32, so nothing mistypes — the
//@ mechanism: precondition simply constrains the WRONG field. Written, it assumes `a == 5`;
//@ mechanism: read positionally in source order it assumes `b == 5`, which is what the body
//@ mechanism: returns.
//@ accept-means: an assumption silently attaches to a different field than the one named, so a
//@ accept-means: precondition can be made to imply a postcondition it does not imply.
//@ WHY THE CONTRACT IS FALSE: the precondition pins `a`, the body returns `b`, and
//@ WHY THE CONTRACT IS FALSE: `f(Q::C { a: 5, b: 0 })` returns 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub enum Q { C { a: u32, b: u32 }, N }
#[requires(match q { Q::C { b: bb, a: aa } => aa@ == 5, Q::N => false })]
#[ensures(result@ == 5)]
pub fn f(q: Q) -> u32 { match q { Q::C { a: _a, b } => b, Q::N => 0 } }
