//@ expect: verify
//@ mechanism: the true control of structpat_let_destructure_ensures_reorder: the same reordered
//@ mechanism: `let` in the ensures, and a body that returns the field the binding names.
//@ accept-means: n/a (control).
//@ teeth: INFERRED from the requires control (same lowering, same binding): under the
//@ teeth: written-position reading `aa` denotes `b` (0) and the postcondition fails.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[requires(s.a@ == 5 && s.b@ == 0)]
#[ensures({ let S { a: aa, b: _bb } = s; result@ == aa@ })]
pub fn g(s: S) -> u32 { match s { S { b: _b, a } => a } }
