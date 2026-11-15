//@ expect: reject
//@ verdict: unknown
//@ refused-with: a `..` rest pattern followed by further positional fields in `P(..)`
//@ fixed-by: 380d8cd3
//@ mechanism: `P(.., a)` on a tuple struct names the LAST field. The parser consumed the `..`
//@ mechanism: and kept `a` at its WRITTEN index, 0, so the pattern read the FIRST field. No
//@ mechanism: metadata survived for the driver to place or the encoder gate to refuse: the
//@ mechanism: same shape as a reordered named-field pattern, on tuple constructors. Now refused
//@ mechanism: by name, because specification text cannot see the declared arity.
//@ accept-means: a positional binding after `..` denotes a different field than the one it names.
//@ WHY THE CONTRACT IS FALSE: `P(.., a)` pins `p.1`; `g` returns `p.0`.
//@ teeth: MEASURED on 0d0aaba9 (the commit before the fix; TRUST_WP_HARNESS_PROFILE=debug):
//@ teeth: ACCEPTED, exit 0, while the true twin returning `p.1` FAILED, exit 1.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct P(pub u32, pub u32);

#[requires(match p { P(.., a) => a@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(p: P) -> u32 { p.0 }
