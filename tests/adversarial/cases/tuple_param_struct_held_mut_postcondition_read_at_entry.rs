//@ expect: reject
//@ verdict: unknown
//@ refused-with: a `&mut` a parameter holds without being it has no placement
//@ mechanism: a tuple parameter holds a `&mut` through a struct's field (`t: (W, i32)` with
//@ mechanism: `W { r: &mut i32 }`). The state rule classified a parameter by the types its type
//@ mechanism: names as generic arguments only, so `t` was a `Value`, and `*t.0.r` was read at entry
//@ mechanism: on both sides of `old` where `*t.0` of `t: (&mut i32, i32)` is refused (D-101).
//@ accept-means: a postcondition read of a `&mut` a parameter holds through a struct's field was
//@ accept-means: placed at entry.
//@ WHY THE CONTRACT IS FALSE: the clause names `t` inside `old`, so it is in the pre-Creusot dialect:
//@ WHY THE CONTRACT IS FALSE: `*t.0.r` outside `old` is the value left, one more than `old(*t.0.r)`.
//@ fixed-by: D-181 — whether a parameter holds a `&mut` is decided by the walk that decides it for a
//@ fixed-by: pattern binding, through fields too, so `t` is `HeldMutable` and D-101 refuses the read.
//@ teeth: ACCEPTED (exit 0, `f verified`) at the head D-181 was written on, and on a build of D-181
//@ teeth: without its classification change (the discovery check alone does not see `t` as holding
//@ teeth: a `&mut`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W<'a> {
    pub r: &'a mut i32,
}

#[requires(*t.0.r < 100i32 && *t.0.r > -100i32)]
#[ensures(*t.0.r == old(*t.0.r))]
pub fn f(t: (W, i32)) {
    *t.0.r += 1;
}
