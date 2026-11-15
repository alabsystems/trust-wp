//@ expect: verify
//@ mechanism: the over-refusal guard for the rest refusal: a TRAILING `..` (`P(a, ..)`) leaves
//@ mechanism: every written element at its declared index, so it must still parse and verify.
//@ accept-means: n/a (control).
//@ teeth: n/a — control; MEASURED verified on 0d0aaba9.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct P(pub u32, pub u32);

#[requires(match p { P(a, ..) => a@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(p: P) -> u32 { p.0 }
