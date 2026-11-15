//@ expect: reject
//@ verdict: unknown
//@ refused-with: a postcondition reads that `&mut` only through `*`, `^` or `@`
//@ mechanism: a postcondition reads a field of the `&mut` a tuple parameter holds, through Rust's
//@ mechanism: auto-deref (`t.0.f` of `t: (&mut S, i32)`). D-101 refuses `*`, `^` and `@` read through
//@ mechanism: such a `&mut`, but a field read is none of those, and the lane reads it at entry.
//@ accept-means: a postcondition read of a `&mut` a parameter holds without being it was placed, where
//@ accept-means: contract-syntax.md says every such read is refused in either dialect.
//@ WHY THE CONTRACT IS FALSE: the clause names `t`, which holds a `&mut`, inside `old`, so it is in the
//@ WHY THE CONTRACT IS FALSE: pre-Creusot dialect: `t.0.f` outside `old` is the value left, one more than
//@ WHY THE CONTRACT IS FALSE: `old(t.0.f)`.
//@ fixed-by: D-181 — discovery follows each field access on `t` over its type; `t.0.f` steps through
//@ fixed-by: the held `&mut`, so the clause is refused, as D-179 refuses `p.f` of a destructured `p`.
//@ teeth: ACCEPTED (exit 0, `g verified`) on the merge of wp-campaign into wp-s117 and at the head
//@ teeth: D-181 was written on, where the full corpus listed it among the false accepts. The twin
//@ teeth: `t.0.f == old(t.0.f) + 1` is FAILED there, so the lane read `t.0.f` at entry.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub f: i32,
}

#[requires(t.0.f < 100i32)]
#[ensures(t.0.f == old(t.0.f))]
pub fn g(t: (&mut S, i32)) {
    t.0.f += 1;
}
