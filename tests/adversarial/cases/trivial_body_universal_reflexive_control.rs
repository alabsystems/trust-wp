//@ expect: verify
//@ mechanism: isolating twin of `trivial_body_universal_false` — the same trivial body and binder with a TRUE claim must be proved
//@ teeth: over-refusal control — measured `assumed (axiom-only function ...)`, exit 2, before the fix; `verified ✓` after it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(forall<i: u32> i == i)]
pub fn refl() {}
