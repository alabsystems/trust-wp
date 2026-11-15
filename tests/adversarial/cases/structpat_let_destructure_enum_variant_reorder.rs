//@ expect: reject
//@ fixed-by: 0d0aaba9
//@ mechanism: the `let` destructuring of a single-variant ENUM, `let E::C { a: aa, b: _bb } = e;`
//@ mechanism: (irrefutable, so legal Rust). The positional lowering read `__trust_wp_tuple_get_0`
//@ mechanism: of an enum value; the pattern now travels whole to placement, which resolves the
//@ mechanism: variant's declaration through the constructor table.
//@ accept-means: a binding denotes the variant's first declared field, not the one it names.
//@ WHY THE CONTRACT IS FALSE: the precondition pins `a`; `g` returns `b`.
//@ teeth: MEASURED on the merged tip 4e4613be (TRUST_WP_HARNESS_PROFILE=debug, ay a9c919158a):
//@ teeth: ACCEPTED, exit 0 — a live false accept. After the fix: unknown (quantifier-unhandled),
//@ teeth: exit 2 — fail-closed, not a counterexample; see the control for the completeness cost.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub enum E { C { b: u32, a: u32 } }

#[requires({ let E::C { a: aa, b: _bb } = e; aa@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(e: E) -> u32 { match e { E::C { b, a: _a } => b } }
