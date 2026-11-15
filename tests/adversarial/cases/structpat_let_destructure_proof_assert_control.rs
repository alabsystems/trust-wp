//@ expect: verify
//@ mechanism: the true control of structpat_let_destructure_proof_assert_reorder: the
//@ mechanism: precondition pins the field the `let` binding names, so the assertion holds.
//@ accept-means: n/a (control).
//@ teeth: INFERRED from the requires control (same lowering, same binding): under the
//@ teeth: written-position reading `aa` denotes `b` (0) and the assertion fails.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[requires(s.a@ == 5 && s.b@ == 0)]
pub fn g(s: S) { proof_assert!({ let S { a: aa, b: _bb } = s; aa@ == 5 }); }
