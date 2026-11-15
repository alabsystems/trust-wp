//@ expect: reject
//@ verdict: unknown
//@ refused-with: than the candidate table keeps
//@ mechanism: the s82 fix's own candidate table reopening the hole it closes. The table keys
//@ mechanism: every constructor spelling to the DISTINCT field lists that answer to it, capped
//@ mechanism: at MAX_CTOR_CANDIDATES = 8. Eight decoy enums declare a variant spelled `C`
//@ mechanism: before the real one, so the ninth list — `real::E::C`'s actual `{b, a}` — did not
//@ mechanism: fit and was DROPPED. `place_named_fields` then resolved the pattern against a
//@ mechanism: surviving decoy and placed `aa` at index 0, which is not this constructor's.
//@ mechanism: The same contract with 0 or 2 decoys rejected correctly; only the decoy COUNT
//@ mechanism: varies, which is what makes this the table's defect and not the pattern's.
//@ accept-means: a bounded lookup table became a silent fallback — the one thing
//@ accept-means: `place_named_fields` documents it does not have — so a pattern is placed at
//@ accept-means: some other constructor's indices exactly when the real one is crowded out.
//@ WHY THE CONTRACT IS FALSE: `real::E::C` declares `{ b: A, a: u32 }`, so `aa` binds `a: u32`
//@ WHY THE CONTRACT IS FALSE: and `u32` has no `view()`. Only the source-order misreading binds
//@ WHY THE CONTRACT IS FALSE: `aa` to `b: A`, whose `view()` answers 5.
//@ teeth: the rejection is trust-wp's own named refusal, pinned by `refused-with:` to a
//@ teeth: `trust-wp:` output line, so a rustc compile error cannot stand in. The crate compiles:
//@ teeth: every decoy is legal Rust and `C` is in scope by `use`. Measured ACCEPTED (exit 0,
//@ teeth: `g verified ✓`) before the cap recorded its own truncation.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A;
impl A { #[logic(open)] pub fn view(self) -> Int { pearlite!{5} } }

pub mod m2 { pub enum E { C { a: u32, b: u32 } } }
pub mod m3 { pub enum E { C { a: u32, b: u32, c: u32 } } }
pub mod m4 { pub enum E { C { a: u32, b: u32, c: u32, d: u32 } } }
pub mod m5 { pub enum E { C { a: u32, b: u32, c: u32, d: u32, e: u32 } } }
pub mod m6 { pub enum E { C { a: u32, b: u32, c: u32, d: u32, e: u32, f: u32 } } }
pub mod m7 { pub enum E { C { a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32 } } }
pub mod m8 { pub enum E { C { a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32 } } }
pub mod m9 { pub enum E { C { a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32, i: u32 } } }

pub mod real { pub enum E { C { b: super::A, a: u32 } } }

use real::E::C;

#[ensures(match e { C { a: aa, b: _bb } => aa.view() == 5 })]
pub fn g(e: real::E) {}
