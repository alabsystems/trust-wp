//@ expect: reject
//@ mechanism: `resolve(g)` of the binder in Creusot's FnMut idiom `exists<g: F>
//@ mechanism: f.postcondition_mut(args, g, result) && resolve(g)` is expanded to `*g == ^g`, and the
//@ mechanism: wrapper's binder arm collapsed both onto the binder whatever its sort, so the claim
//@ mechanism: that the state after the call is resolved was `true` whether or not the function drops
//@ mechanism: that state.
//@ accept-means: a function that RETURNS the closure after calling it is credited with the claim
//@ accept-means: that the returned state's captured borrows are resolved.
//@ WHY THE CONTRACT IS FALSE: `keep_closure` returns the state `g` it reached; a closure capturing
//@ WHY THE CONTRACT IS FALSE: `&mut x` keeps that borrow in `g`, and its holder decides its final
//@ WHY THE CONTRACT IS FALSE: value by calling it again (`*g.x == ^g.x` fails when the caller calls
//@ WHY THE CONTRACT IS FALSE: the returned closure once more), so `resolve(g)` is no fact of the call.
//@ fixed-by: D-126 (the final value of a quantifier's binder annotated at a sort whose shape may hold
//@ fixed-by: a borrow, a type parameter included, is refused, not collapsed onto the binder)
//@ teeth: MEASURED (debug driver, ay 57a37e51): bdbba131 verifies keep_closure (ACCEPTED);
//@ teeth: on D-126 it is refused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{prelude::*, resolve::Resolve};

#[requires(f.precondition(()))]
#[ensures(exists<g: F> f.postcondition_mut((), g, ()) && resolve(g))]
pub fn keep_closure<F: FnMut()>(mut f: F) -> F {
    f();
    f
}
