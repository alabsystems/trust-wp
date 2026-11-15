//@ expect: verify
//@ mechanism: a variant reached through a `pub use` RE-EXPORT (`r::E::C`), in declaration
//@ mechanism: order. It guards the other half of the v3 change: the flat name->index fallback
//@ mechanism: is gone, so every constructor spelling now has to be tied to a real declaration
//@ mechanism: — by the resolver or by the path table — or the row is lost. This spelling
//@ mechanism: verified before the change and has to keep verifying after it.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
//@ teeth: n/a — over-refusal control. `verified ✓` before and after v3.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m { pub enum E { C { b: u32, a: u32 }, N } }
pub mod r { pub use super::m::E; }
pub struct D { pub a: u32, pub b: u32 }

#[requires(match e { r::E::C { a: aa, b: _bb } => aa@ == 5, r::E::N => false })]
#[ensures(result@ == 5)]
pub fn g(e: m::E, _d: D) -> u32 { match e { m::E::C { b: _b, a } => a, m::E::N => 0 } }
