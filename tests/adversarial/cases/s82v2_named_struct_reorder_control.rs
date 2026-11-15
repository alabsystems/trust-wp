//@ expect: verify
//@ mechanism: the isolating twin of `s82v2_selfpath_struct_control`: byte-for-byte the same
//@ mechanism: crate with the struct spelled `S` instead of `Self`. A reordered braced-struct
//@ mechanism: pattern IS placed at its declared indices, so this one verifies — which is what
//@ mechanism: pins the twin's failure to the `Self` spelling and not to the reordering.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
//@ teeth: n/a — over-refusal control. Verifies on campaign tip and after v2.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S { pub b: u32, pub a: u32 }

impl S {
    #[requires(match self { S { a: aa, b: _bb } => aa@ == 1 })]
    #[ensures(result@ == 1)]
    pub fn get(self) -> u32 { self.a }
}
