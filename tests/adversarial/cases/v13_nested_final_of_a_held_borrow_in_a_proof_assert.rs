//@ expect: reject
//@ mechanism: `^` of a borrow held two field projections deep in a `&mut` parameter, in a
//@ mechanism: `proof_assert!` (the contract lane's placement refusal reads no assertion). The
//@ mechanism: encoder's Phase 1f asked the annotation of the outer projection's BASE, which a
//@ mechanism: projection (`x.s`) does not carry, so the chain was never refused and Phase 3
//@ mechanism: distributed `^` down to `(^x).s.m`: the field the OUTER borrow is left with, which an
//@ mechanism: empty body leaves equal to `(*x).s.m`. ay proved the false assertion (unsat on the
//@ mechanism: wire), and only the strict proof-authority gate withheld the credit; through a tuple
//@ mechanism: field (`^x.t.0`) the assertion was credited.
//@ accept-means: an assertion that a borrow the caller keeps is resolved is credited (or proved by ay
//@ accept-means: and withheld by a certificate gate alone).
//@ WHY THE CONTRACT IS FALSE: `x.s.m` is the caller's borrow; its final value is decided after the
//@ WHY THE CONTRACT IS FALSE: call, so `^x.s.m == *x.s.m` is no fact of the function.
//@ fixed-by: D-128 (Phase 1f types a projection chain from the declarations, and refuses `^` of a
//@ fixed-by: field that may be a mutable reference at any depth, and of a chain through a reference
//@ fixed-by: it cannot type); D-129 (the assertion's text is refused first: no operand of these `^`
//@ fixed-by: is a borrow named as one)
//@ refused-with: proof_assert in creusot_test::a1 error: final value refused
//@ teeth: MEASURED (debug driver): before D-128 e1's assertion (a borrow in a tuple field of the
//@ teeth: holder) was VERIFIED, and a1, b1 and c1 were `unknown (proof_assert slice lacks exact strict
//@ teeth: proof authority)` with `ay_result=unsat` on the wire; D-128 refused each at encoding, and
//@ teeth: D-129 refuses each assertion's text before encoding, as the refused-with line pins for a1. d1
//@ teeth: (a borrow held through an inner borrow) was refused before and after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

pub struct N<'a> {
    pub s: M<'a>,
}

pub struct MB<'a> {
    pub m: &'a mut bool,
}

pub struct NB<'a> {
    pub s: MB<'a>,
}

pub fn a1(x: &mut N<'_>) {
    proof_assert!(^x.s.m == *x.s.m);
}

pub fn b1(x: &mut NB<'_>) {
    proof_assert!(^x.s.m == *x.s.m);
}

pub fn c1(x: &mut N<'_>) {
    let y = 1i32;
    proof_assert!(y == 1i32 && ^x.s.m == *x.s.m);
}

pub struct R<'a, 'b> {
    pub r: &'a mut M<'b>,
}

pub fn d1(x: &mut R<'_, '_>) {
    proof_assert!(^x.r.m == *x.r.m);
}

pub struct T<'a> {
    pub t: (&'a mut i32, i32),
}

pub fn e1(x: &mut T<'_>) {
    proof_assert!(^x.t.0 == *x.t.0);
}
