//@ expect: verify
//@ mechanism: the primary over-refusal guard: an enum-variant pattern in DECLARATION order, the
//@ mechanism: shape ordinary code writes constantly. Source order already equals declaration
//@ mechanism: order, so this verifies on main; a fail-closed refusal that cannot resolve enum
//@ mechanism: variant fields would take it down with the reordered ones.
//@ accept-means: n/a (control).
//@ teeth: n/a — over-refusal control; verifies on main.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub enum U { C { a: u32, b: u32 }, N }
#[requires(match u { U::C { a: aa, b: bb } => aa@ == 5 && bb@ == 7, U::N => false })]
#[ensures(result@ == 5)]
pub fn f(u: U) -> u32 { match u { U::C { a, b: _b } => a, U::N => 0 } }
