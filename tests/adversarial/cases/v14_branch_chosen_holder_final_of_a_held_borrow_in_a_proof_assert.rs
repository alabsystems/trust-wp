//@ expect: reject
//@ mechanism: `^` of a declared `&mut` field whose holder an `if` or `match` chooses among a `&mut`
//@ mechanism: parameter, its dereference or its final value (`^(if c { x } else { x }).m`,
//@ mechanism: `^(if c { *x } else { *x }).m`). `projection_place_sort` gave an `Ite`/`Match` holder
//@ mechanism: no sort and no reference, so Phase 1f did not refuse, and Phase 3 distributed `^` into
//@ mechanism: the branches: `(^x).m`, the field the OUTER borrow is left with. ay proved each (unsat
//@ mechanism: on the wire); whether the credit stood depended on the strict proof-authority gate
//@ mechanism: from one run to the next (D-129).
//@ accept-means: an assertion that the caller's borrow `x.m` is resolved is credited (or proved by
//@ accept-means: ay and withheld by a certificate gate alone).
//@ WHY THE CONTRACT IS FALSE: `x.m` is the caller's borrow; the caller writes through it after the
//@ WHY THE CONTRACT IS FALSE: call (`let mut m = M { m: &mut a }; ite(&mut m, true); *m.m = 7;`), so its
//@ WHY THE CONTRACT IS FALSE: final value is 7 while `*x.m` is 1 at the assertion.
//@ fixed-by: D-129 (an assertion's final read of a value no name denotes as a borrow is refused; Phase
//@ fixed-by: 1f types an `if`/`match` holder from its branches)
//@ refused-with: proof_assert in creusot_test::ite error: final value refused
//@ teeth: MEASURED (debug driver, ay 57a37e51): on 2c859203 `matched`'s assertion was VERIFIED and
//@ teeth: ite, ite_deref and match_deref were unknown with ay_result=unsat (strict proof-authority gate);
//@ teeth: with D-129 all four are refused before encoding.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

pub fn ite(x: &mut M<'_>, c: bool) {
    proof_assert!(^(if c { x } else { x }).m == *x.m);
}

pub fn matched(x: &mut M<'_>, c: bool) {
    proof_assert!(^(match c { true => x, false => x }).m == *x.m);
}

pub fn ite_deref(x: &mut M<'_>, c: bool) {
    proof_assert!(^(if c { *x } else { *x }).m == *(*x).m);
}

pub fn match_deref(x: &mut M<'_>, c: bool) {
    proof_assert!(^(match c { true => *x, false => *x }).m == *(*x).m);
}
