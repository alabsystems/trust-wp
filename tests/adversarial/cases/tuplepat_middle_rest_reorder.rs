//@ expect: reject
//@ verdict: unknown
//@ refused-with: a `..` rest pattern followed by further positional fields in `P(..)`
//@ fixed-by: 380d8cd3
//@ mechanism: `P(_a, .., c)` on a THREE-field tuple struct: `c` names field 2, the dropped `..`
//@ mechanism: left it at written index 1.
//@ accept-means: a positional binding after `..` denotes a different field than the one it names.
//@ WHY THE CONTRACT IS FALSE: the precondition pins `p.2`; `g` returns `p.1`.
//@ teeth: MEASURED on 0d0aaba9: ACCEPTED, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct P(pub u32, pub u32, pub u32);

#[requires(match p { P(_a, .., c) => c@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(p: P) -> u32 { p.1 }
