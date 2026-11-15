//@ expect: verify
//@ mechanism: the over-refusal guard for the `let` lowering: a tuple-style constructor in a
//@ mechanism: `let` (`let P(_x, y) = p;`, the list_index_mut.rs shape) keeps its positional
//@ mechanism: read, because unnamed fields are declared by position.
//@ accept-means: n/a (control).
//@ teeth: n/a — control; MEASURED verified on 0d0aaba9.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct P(pub u32, pub u32);

#[requires({ let P(_x, y) = p; y@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(p: P) -> u32 { p.1 }
