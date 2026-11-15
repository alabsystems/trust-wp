//@ expect: verify
//@ xfail: completeness — the PRICE of the candidate-cap refusal, paid deliberately. Nine
//@ xfail: constructors answer to `C`; all nine declare `a` first with arity 3, so
//@ xfail: `C { a: aa, .. }` is placed identically by every one of them and the answer is not in
//@ xfail: doubt. The ninth still does not fit under MAX_CTOR_CANDIDATES, and a capped entry is
//@ xfail: refused because a dropped candidate CAN be the real constructor and the table cannot
//@ xfail: tell the two situations apart. MEASURED: campaign tip did not verify this either (ay
//@ xfail: withheld its proof), so no provable row is lost here — but the refusal is a real
//@ xfail: narrowing and is recorded as one. Retire this directive by raising or removing the
//@ xfail: cap, never by making truncation silent again (`s82v2_ctor_candidate_cap`).
//@ mechanism: over-refusal control for the D1 fix, isolated: only the DECOY COUNT separates it
//@ mechanism: from a crate whose candidate set fits.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m1 { pub enum E { C { a: u32, b: u32, c1: u32 } } }
pub mod m2 { pub enum E { C { a: u32, b: u32, c2: u32 } } }
pub mod m3 { pub enum E { C { a: u32, b: u32, c3: u32 } } }
pub mod m4 { pub enum E { C { a: u32, b: u32, c4: u32 } } }
pub mod m5 { pub enum E { C { a: u32, b: u32, c5: u32 } } }
pub mod m6 { pub enum E { C { a: u32, b: u32, c6: u32 } } }
pub mod m7 { pub enum E { C { a: u32, b: u32, c7: u32 } } }
pub mod m8 { pub enum E { C { a: u32, b: u32, c8: u32 } } }
pub mod real { pub enum E { C { a: u32, b: u32, z: u32 } } }

use real::E::C;

#[requires(match e { C { a: aa, .. } => aa@ == 1 })]
#[ensures(result@ == 1)]
pub fn g(e: real::E) -> u32 { match e { real::E::C { a, b: _b, z: _z } => a } }
