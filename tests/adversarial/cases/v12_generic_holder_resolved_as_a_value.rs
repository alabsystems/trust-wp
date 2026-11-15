//@ expect: reject
//@ mechanism: `sort_embeds_mut_ref` answers the collapse guard's question, and says a generic ADT's
//@ mechanism: unsubstituted type-parameter field embeds no `&mut` (there is no prophecy slot to
//@ mechanism: invert in the generic definition). `encode_resolve` read that answer as "holds no
//@ mechanism: borrow" and resolved `x: S<A>` as the by-value `true`, although the claim is made for
//@ mechanism: every instantiation, `A = &mut i32` included.
//@ accept-means: a generic function returning (a part of) its argument is credited with the claim
//@ accept-means: that the borrows the argument may hold are resolved at the return.
//@ WHY THE CONTRACT IS FALSE: at `A = &mut i32` (or `B = &mut i32`) the returned value holds the
//@ WHY THE CONTRACT IS FALSE: caller's borrow, whose final value the caller decides after the call.
//@ fixed-by: D-126 (`sort_holds_no_borrow` asks the sort's own shape: a datatype may hold a borrow
//@ fixed-by: its declaration does not show)
//@ teeth: MEASURED (debug driver, ay 57a37e51): bdbba131 verifies keep, keep_result and
//@ teeth: take_b (ACCEPTED); on D-126 each is refused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S<A> {
    pub a: A,
}

pub struct P<A, B> {
    pub a: A,
    pub b: B,
}

#[ensures(resolve(x))]
pub fn keep<A>(x: S<A>) -> S<A> {
    x
}

#[ensures(resolve(result))]
pub fn keep_result<A>(x: S<A>) -> S<A> {
    x
}

#[ensures(resolve(x))]
pub fn take_b<A, B>(x: P<A, B>) -> B {
    x.b
}
