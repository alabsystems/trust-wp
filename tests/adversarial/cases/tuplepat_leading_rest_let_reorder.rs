//@ expect: reject
//@ verdict: unknown
//@ refused-with: a `..` rest pattern followed by further positional fields in `P(..)`
//@ fixed-by: 380d8cd3
//@ mechanism: tuplepat_leading_rest_match_reorder through a `let`: `let P(.., a) = p;`. Same
//@ mechanism: parse, same dropped `..`, same written-index read.
//@ accept-means: as its match twin.
//@ WHY THE CONTRACT IS FALSE: `P(.., a)` pins `p.1`; `g` returns `p.0`.
//@ teeth: MEASURED on 0d0aaba9: ACCEPTED, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct P(pub u32, pub u32);

#[requires({ let P(.., a) = p; a@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(p: P) -> u32 { p.0 }
