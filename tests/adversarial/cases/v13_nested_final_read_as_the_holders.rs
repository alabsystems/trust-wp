//@ expect: reject
//@ mechanism: `^(x.m)` of `x: &mut M` whose field `m` is itself a `&mut i32` is the final value of that
//@ mechanism: INNER borrow, which the caller decides. The contract lane placed it as the field the
//@ mechanism: outer borrow is left with, and the wrapper distributes `^` into the field getter's
//@ mechanism: argument (Creusot's rule for a place reborrowed out of `*x`): `^(x.m) == *(x.m)` read as
//@ mechanism: `(^x).m == (*x).m`, true of an empty body. The same in a `proof_assert!`, where the
//@ mechanism: encoder also read `resolve(x.m)` as `(*x).m == (^x).m`.
//@ accept-means: a function is credited with the claim that a borrow its caller keeps (and may write
//@ accept-means: through after the call) is resolved at the return.
//@ WHY THE CONTRACT IS FALSE: `x.m` (resp. `x.0`) is the caller's inner borrow; the caller may write 5
//@ WHY THE CONTRACT IS FALSE: through it after the call while its value at the call is 3.
//@ fixed-by: D-127 (a final value read of a value held through a `&mut` parameter is refused where
//@ fixed-by: the contract is placed; `^` of a field that may be a mutable reference, projected
//@ fixed-by: through a reference, is refused by the encoder)
//@ teeth: MEASURED (debug driver): before D-127 paren_inner and paren_tuple verified, and so did
//@ teeth: the `proof_assert!` in assert_resolve_inner (assert_inner's was unknown, short of strict
//@ teeth: proof authority); D-127 refuses all four.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

#[ensures(^(x.m) == *(x.m))]
pub fn paren_inner(x: &mut M<'_>) {}

#[ensures(^(x.0) == *(x.0))]
pub fn paren_tuple(x: &mut (&mut i32, i32)) {}

pub fn assert_inner(x: &mut M<'_>) {
    proof_assert!(^x.m == *x.m);
}

pub fn assert_resolve_inner(x: &mut M<'_>) {
    proof_assert!(resolve(x.m));
}
