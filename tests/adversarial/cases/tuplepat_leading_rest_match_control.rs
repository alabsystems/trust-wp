//@ expect: verify
//@ xfail: refused by name — the parser cannot place a field after `..` without the declared
//@ xfail: arity; this records the completeness cost of the fail-closed refusal
//@ mechanism: the true twin of tuplepat_leading_rest_match_reorder: `g` returns the field
//@ mechanism: `P(.., a)` names. On the positional read this FAILED while its false twin verified.
//@ accept-means: n/a (control).
//@ teeth: MEASURED on 0d0aaba9: failed, exit 1 — the other half of the pair.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct P(pub u32, pub u32);

#[requires(match p { P(.., a) => a@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(p: P) -> u32 { p.1 }
