//@ expect: reject
//@ verdict: failed
//@ mechanism: a named-field struct LITERAL — not a pattern — inside a LOGIC FUNCTION BODY.
//@ mechanism: The parser encodes a literal's field names into the constructor name the same
//@ mechanism: way it encodes a pattern's (`contract_parser/helpers/expressions.rs`), and the
//@ mechanism: logic-fn body path placed neither. Every s82 case before v4 used a PATTERN, so
//@ mechanism: this sub-shape was not in the corpus at all.
//@ accept-means: a logic constructor puts each value in the wrong field, so any contract that
//@ accept-means: projects a field out of it reads a value that was written elsewhere.
//@ WHY THE CONTRACT IS FALSE: `mk` writes `a: p, b: q`, so `mk(x, y).b` is `y == 0`. The
//@ WHY THE CONTRACT IS FALSE: postcondition claims it is 5.
//@ teeth: A/B MEASURED on the pre-s82 campaign tip 7bf6aabb: ACCEPTED, exit 0 — a LIVE false
//@ teeth: accept, and one no committed case covered. On the s82 v4 head: failed, exit 1.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub b: u32,
    pub a: u32,
}

#[logic(open)]
pub fn mk(p: u32, q: u32) -> S {
    pearlite! { S { a: p, b: q } }
}

#[requires(x@ == 5 && y@ == 0)]
#[ensures(mk(x, y).b@ == 5)]
pub fn f(s: S, x: u32, y: u32) -> u32 {
    s.a
}
