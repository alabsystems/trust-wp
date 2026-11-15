//@ expect: verify
//@ xfail: completeness — MEASURED FAILED on campaign tip 16d941f1 and identically after the s82
//@ xfail: v1 and v2 fixes. A braced STRUCT spelled `Self { .. }` is placed at its declared
//@ xfail: indices correctly, but the rewrite keeps the constructor NAME as written, and the
//@ xfail: encoder's `short_constructor_name` of `Self` is `Self`, which matches no datatype
//@ xfail: constructor. `Self::C` survives because its short name is `C`, which is why the enum
//@ xfail: arm works and this one does not. The gap is FAIL-CLOSED — its reordered twin fails
//@ xfail: too, so nothing false is proved — and PRE-EXISTING: s82 neither caused it nor closed
//@ xfail: it. Retire this directive when the rewrite emits the constructor's canonical path.
//@ mechanism: over-refusal control: `Self { a: aa, b: _bb }` on `S { b: u32, a: u32 }`, body
//@ mechanism: returns `a`. Its twin `s82v2_named_struct_reorder_control` is the identical crate
//@ mechanism: with the struct spelled `S` instead of `Self`, and that one VERIFIES — which is
//@ mechanism: what isolates the gap to the `Self` spelling rather than to the reordering.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S { pub b: u32, pub a: u32 }

impl S {
    #[requires(match self { Self { a: aa, b: _bb } => aa@ == 1 })]
    #[ensures(result@ == 1)]
    pub fn get(self) -> u32 { self.a }
}
