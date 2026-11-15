//@ expect: verify
//@ xfail: ay computes the UNSAT and withholds it (proof-trusted), exit 2 — a completeness cost
//@ xfail: of the encoder's single-variant enum match, not of the parser lowering
//@ mechanism: the true control of structpat_let_destructure_enum_variant_reorder.
//@ accept-means: n/a (control).
//@ teeth: MEASURED on the merged tip 4e4613be: unknown, exit 2 as well — the withholding predates
//@ teeth: the lowering change.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub enum E { C { b: u32, a: u32 } }

#[requires({ let E::C { a: aa, b: _bb } = e; aa@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(e: E) -> u32 { match e { E::C { b: _b, a } => a } }
