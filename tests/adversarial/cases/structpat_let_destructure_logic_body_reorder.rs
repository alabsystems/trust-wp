//@ expect: reject
//@ verdict: failed
//@ mechanism: `let S { a: aa, b: _bb } = s;` inside a LOGIC FUNCTION BODY. The body is parsed
//@ mechanism: by the same contract parser, so the same positional `let` lowering discarded the
//@ mechanism: constructor name there; the logic-fn placement pass never saw a pattern to place.
//@ accept-means: a logic function reads a different field than the one it names.
//@ WHY THE CONTRACT IS FALSE: `pick` names `a`; `g` returns `b`.
//@ teeth: MEASURED on the merged tip 4e4613be: failed, exit 1 (the reviewer's ld02) — on this
//@ teeth: path the positional read failed the FALSE contract, and ALSO failed its true control
//@ teeth: (ld02c): the pair shows the binding denoted the wrong field in both directions.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[logic(open)]
pub fn pick(s: S) -> Int { pearlite! { let S { a: aa, b: _bb } = s; aa@ } }

#[requires(pick(s) == 5)]
#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 { match s { S { b, a: _a } => b } }
