//@ expect: reject
//@ verdict: unknown
//@ mechanism: `super::super::E::C` — two levels of module-relative prefix. It is here because
//@ mechanism: enumerating `self::` and `super::` would have left it, and the next form after
//@ mechanism: it: the fix has to be the resolver's answer rather than a longer list.
//@ accept-means: the placement still depends on which path prefixes someone listed.
//@ WHY THE CONTRACT IS FALSE: the precondition constrains `a`; the body returns `b`.
//@ teeth: measured ACCEPTED, exit 0 on the s82 v2 fix. Its control verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E { C { b: u32, a: u32 }, N }
pub struct D { pub a: u32, pub b: u32 }

pub mod m { pub mod n {
    use creusot_std::prelude::*;
    #[requires(match e { super::super::E::C { a: aa, b: _bb } => aa@ == 5, super::super::E::N => false })]
    #[ensures(result@ == 5)]
    pub fn g(e: crate::E, _d: crate::D) -> u32 { match e { crate::E::C { b, a: _a } => b, crate::E::N => 0 } }
} }
