//@ expect: verify
//@ mechanism: over-refusal control for the CALLER side of a `Self::`-qualified contract. A
//@ mechanism: callee's contract does not stay with the callee: its `requires` becomes an
//@ mechanism: obligation on the caller, and the caller's merged contract is rewritten once, in
//@ mechanism: the CALLER's environment. `caller` is a free function, so `Self` resolves to
//@ mechanism: nothing there unless the rewrite also knows the impls this body calls into.
//@ accept-means: n/a (control) — both contracts are TRUE.
//@ teeth: n/a — over-refusal control. Measured on the s82 v1 fix as `E::get verified ✓` plus
//@ teeth: `caller error: ... no declaration for `Self::C` was found`, exit 2: every method with
//@ teeth: a `Self::Variant` contract poisoned every one of its callers.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E { C { a: u32, b: u32 }, N }

impl E {
    #[requires(match self { Self::C { a: aa, b: _bb } => aa@ == 5, Self::N => false })]
    #[ensures(result@ == 5)]
    pub fn get(self) -> u32 { match self { E::C { a, b: _b } => a, E::N => 0 } }
}

#[requires(match e { E::C { a: aa, b: _bb } => aa@ == 5, E::N => false })]
#[ensures(result@ == 5)]
pub fn caller(e: E) -> u32 { e.get() }
